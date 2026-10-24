/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.O2HTheorem

/-!
# Measure-and-reprogram for a `q`-query adversary

The measure-and-reprogram bound of Don, Fehr, Majenz and Schaffner (CRYPTO 2019,
Theorem 2, single reprogrammed point) for an arbitrary adversary `QAdv m n w q`,
oracle `H : Fin m → Fin n`, point `x₀` and value `θ`. The simulator picks a
slot `(i, b)` among the `2q + 1` slots `Option (Fin q × Bool)`; it runs the
adversary against `H` up to query `i`, measures the query register to obtain
`x`, and continues with the reprogrammed oracle `H[x ↦ θ]` from query `i`
(`b = false`) or from query `i + 1` (`b = true`); the slot `none` measures the
query register after the last unitary. The adversary's output is read by
measuring its query register (the output `x'`) and then its final projector,
which plays the predicate `V(x₀, θ, ·)`.

## Main definitions

* `measXOps m n w`, `measX m n w` — the measurement of the query register's
  first factor, with outcomes `Fin m`
* `measChain O M G R j q U` — the chain of `U` with the oracle `O`, the
  instrument `M` after `U_j`, the oracle `R a` at query `j` and `G a` after it
* `simOp o g r P j q U` — the operator of `measChain` on the outcome `a`
* `simChain A H θ t`, `simRun A H θ t` — the simulator on the slot `t`, and the
  simulator followed by the adversary's output measurements, returning
  `(x, x', accept)`
* `outRun A G` — the run of `A` against `G` with its output measurements,
  returning `(x', accept)`
* `prOutAt A G x₀` — `Pr[x' = x₀ ∧ accept : A^G]`
* `prSimAt A H θ x₀ t`, `prMR A H θ x₀` — the simulator's success probability
  on the slot `t`, and its average over the `2q + 1` slots
* `prSimAcc A H θ x₀ t` — the simulator's probability of measuring `x₀` and
  accepting, with the adversary's output `x'` discarded

## Main results

* `chainOp_eq_add_sum_simOp` — the run operator against the reprogrammed
  oracle is the run operator against `H` plus the signed sum of the `2q`
  simulator operators of the slots `i < q`
* `nrm_sq_le_card_mul_sum_simOp` — the vector form of the bound
* `measure_reprogram` — `Pr[x' = x₀ ∧ accept : A^{H[x₀ ↦ θ]}] / (2q + 1)² ≤
  prMR A H θ x₀`
* `measure_reprogram_acc` — the same bound for the simulator that discards the
  adversary's output `x'` (`prSimAcc`)

## References

* [Don, Fehr, Majenz, Schaffner — Security of the Fiat-Shamir Transformation in
  the Quantum Random-Oracle Model, CRYPTO 2019], Theorem 2
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
  CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Branches of binds with a single contributing outcome -/

section Single

variable {d : ℕ} {α β : Type}

/-- A bind whose continuation has a zero branch at `b` on every outcome other
    than `a₀` has the branch of the single outcome `a₀`. -/
theorem qbind_branch_of_single (I : QComp d α) (f : α → QComp d β) (b : β) (a₀ : α)
    (h : ∀ a, a ≠ a₀ → (f a).branch b = 0) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (QComp.qbind I f).branch b ρ = (f a₀).branch b (I.branch a₀ ρ) := by
  rw [qbind_branch_apply]
  exact tsum_eq_single a₀ fun a ha => by rw [h a ha, LinearMap.zero_apply]

/-- The `true` branch of the event `o = o₀` is the branch of `o₀`. -/
theorem qbind_decide_eq_branch_true [DecidableEq α] (I : QComp d α) (o₀ : α) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (QComp.qbind I fun o => QComp.qpure (decide (o = o₀))).branch true ρ = I.branch o₀ ρ := by
  rw [qbind_branch_of_single I _ true o₀]
  · rw [qpure_branch_apply]; simp
  · intro a ha
    apply LinearMap.ext; intro σ
    rw [qpure_branch_apply]; simp [ha]

end Single

/-! ## The measurement of the query register -/

section MeasX

variable (m n w : ℕ)

/-- The projectors on the singletons of the query register sum to the identity. -/
theorem sum_projS_singleton : ∑ x : Fin m, projS m n w {x} = 1 := by
  ext i j
  simp only [projS_eq_diagonal, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply, indS,
    Finset.mem_singleton]
  by_cases h : i = j
  · simp [h]
  · simp [h]

/-- The measurement of the query register's first factor, with outcomes `Fin m`. -/
def measXOps : ProjectiveMeasurement (m * n * w) (Fin m) where
  op x := projS m n w {x}
  completeness := by
    simp only [projS_conjTranspose, projS_mul_self]
    exact sum_projS_singleton m n w
  self_adjoint x := projS_conjTranspose m n w {x}
  idempotent x := projS_mul_self m n w {x}

/-- The measurement of the query register's first factor as an instrument. -/
def measX : QComp (m * n * w) (Fin m) := projectiveMeasure (measXOps m n w)

theorem measX_branch (x : Fin m) (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (measX m n w).branch x ρ = projS m n w {x} * ρ * (projS m n w {x})ᴴ := rfl

end MeasX

/-! ## The chain with one measurement -/

section MeasChain

variable {d : ℕ} {α : Type}

/-- `U₀ ; O ; ⋯ ; O ; U_j ; M ; R a ; U_{j+1} ; G a ; ⋯ ; G a ; U_q`, returning the
    outcome `a` of the instrument `M`. For `j ≥ q` the instrument follows `U_q`. -/
def measChain (O : QComp d Unit) (M : QComp d α) (G R : α → QComp d Unit) :
    (j q : ℕ) → (Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) → QComp d α
  | 0, 0, U => QComp.qbind (unitaryChannel (U 0)) fun _ => M
  | 0, q + 1, U => QComp.qbind (unitaryChannel (U 0)) fun _ => QComp.qbind M fun a =>
      QComp.qbind (R a) fun _ =>
        QComp.qbind (oracleChain (G a) q (Fin.tail U)) fun _ => QComp.qpure a
  | _ + 1, 0, U => QComp.qbind (unitaryChannel (U 0)) fun _ => M
  | j + 1, q + 1, U => QComp.qbind (unitaryChannel (U 0)) fun _ =>
      QComp.qbind O fun _ => measChain O M G R j q (Fin.tail U)

/-- The operator of `measChain` on one outcome: `o` before the measurement,
    the projector `P` after `U_j`, `r` at query `j` and `g` after it. -/
def simOp (o g r P : Matrix (Fin d) (Fin d) ℂ) :
    (j q : ℕ) → (Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) → Matrix (Fin d) (Fin d) ℂ
  | 0, 0, U => P * U 0
  | 0, q + 1, U => chainOp g q (Fin.tail U) * r * P * U 0
  | _ + 1, 0, U => P * U 0
  | j + 1, q + 1, U => simOp o g r P j q (Fin.tail U) * o * U 0

/-- The branch of `measChain` with unitary oracles and a measurement with
    operators `Pm a` is conjugation by `simOp`. -/
theorem measChain_branch (o : Matrix.unitaryGroup (Fin d) ℂ) (M : QComp d α)
    (Pm : α → Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ a σ, M.branch a σ = Pm a * σ * (Pm a)ᴴ)
    (g r : α → Matrix.unitaryGroup (Fin d) ℂ) (j q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (a : α) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (measChain (unitaryChannel o) M (fun a => unitaryChannel (g a))
        (fun a => unitaryChannel (r a)) j q U).branch a ρ =
      simOp (o : Matrix _ _ ℂ) (g a) (r a) (Pm a) j q U * ρ *
        (simOp (o : Matrix _ _ ℂ) (g a) (r a) (Pm a) j q U)ᴴ := by
  induction j generalizing q ρ with
  | zero =>
    cases q with
    | zero =>
      simp only [measChain, simOp, qbind_unit_branch, unitaryChannel_branch_apply, hM,
        conjTranspose_mul, Matrix.mul_assoc]
    | succ q =>
      simp only [measChain, simOp, qbind_unit_branch]
      rw [qbind_branch_of_single _ _ a a]
      · simp only [qbind_unit_branch, qpure_branch_apply, ite_true,
          oracleChain_unitaryChannel_branch, unitaryChannel_branch_apply, hM,
          conjTranspose_mul, Matrix.mul_assoc]
      · intro a' ha'
        apply LinearMap.ext; intro σ
        simp [qbind_unit_branch, qpure_branch_apply, Ne.symm ha']
  | succ j ih =>
    cases q with
    | zero =>
      simp only [measChain, simOp, qbind_unit_branch, unitaryChannel_branch_apply, hM,
        conjTranspose_mul, Matrix.mul_assoc]
    | succ q =>
      simp only [measChain, simOp, qbind_unit_branch, unitaryChannel_branch_apply, ih,
        conjTranspose_mul, Matrix.mul_assoc]

/-- At the last slot the operator of `measChain` is the projector after the
    chain of `o`. -/
theorem simOp_self (o g r P : Matrix (Fin d) (Fin d) ℂ) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    simOp o g r P q q U = P * chainOp o q U := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [simOp, chainOp, ih, Matrix.mul_assoc]

/-- The telescoping identity: with `g = o + g P − o P`, the chain of `g` is the
    chain of `o` plus, for each query `i`, the operator with the measurement
    before query `i` and `g` at query `i`, minus the one with `o` at query `i`. -/
theorem chainOp_eq_add_sum_simOp {o g P : Matrix (Fin d) (Fin d) ℂ}
    (hg : g = o + g * P - o * P) (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    chainOp g q U =
      chainOp o q U + ∑ i : Fin q, (simOp o g g P i q U - simOp o g o P i q U) := by
  induction q with
  | zero => simp [chainOp]
  | succ q ih =>
    have hg' : ∀ X Y : Matrix (Fin d) (Fin d) ℂ,
        X * g * Y = X * o * Y + X * g * P * Y - X * o * P * Y := by
      intro X Y
      conv_lhs => rw [hg]
      simp only [mul_add, add_mul, mul_sub, sub_mul, Matrix.mul_assoc]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, simOp, chainOp]
    conv_lhs => rw [hg']
    rw [ih (Fin.tail U)]
    simp only [Finset.sum_mul, sub_mul, add_mul, Matrix.mul_assoc]
    abel

end MeasChain

/-! ## Norm inequalities -/

section Norm

variable {d : ℕ}

theorem nrm_neg (v : Fin d → ℂ) : nrm (-v) = nrm v := by
  unfold nrm
  rw [WithLp.toLp_neg, norm_neg]

theorem nrm_sub_le (a b : Fin d → ℂ) : nrm (a - b) ≤ nrm a + nrm b := by
  rw [sub_eq_add_neg, ← nrm_neg b]
  exact nrm_add_le a (-b)

theorem nrm_sum_le {ι : Type} (s : Finset ι) (f : ι → Fin d → ℂ) :
    nrm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, nrm (f i) :=
  Finset.le_sum_of_subadditive nrm nrm_zero.le nrm_add_le s f

end Norm

/-! ## The vector form of the bound -/

section Vector

variable {d : ℕ}

/-- The slot of a simulator index: `i` for `some (i, b)`, `q` for `none`. -/
def mrSlot {q : ℕ} : Option (Fin q × Bool) → ℕ
  | none => q
  | some (i, _) => i

/-- Whether the simulator keeps the original oracle at the measured query:
    `true` exactly for `some (i, true)`. -/
def mrKeep {q : ℕ} : Option (Fin q × Bool) → Bool
  | some (_, true) => true
  | _ => false

theorem card_mrIndex (q : ℕ) : Fintype.card (Option (Fin q × Bool)) = 2 * q + 1 := by
  simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-- The measure-and-reprogram bound on vectors: with `g = o + g P − o P`, the
    event vector `F P C_g ψ` of the chain of `g` has squared norm at most
    `2q + 1` times the sum over the slots of the squared norms of the event
    vectors of the simulator operators. -/
theorem nrm_sq_le_card_mul_sum_simOp {o g P F : Matrix (Fin d) (Fin d) ℂ}
    (hg : g = o + g * P - o * P) (hP : P * P = P) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (ψ : Fin d → ℂ) :
    nrm ((F * P * chainOp g q U) *ᵥ ψ) ^ 2 ≤
      (2 * q + 1 : ℝ) * ∑ t : Option (Fin q × Bool),
        nrm ((F * P * simOp o g (if mrKeep t then o else g) P (mrSlot t) q U) *ᵥ ψ) ^ 2 := by
  set e : Option (Fin q × Bool) → (Fin d → ℂ) := fun t =>
    (F * P * simOp o g (if mrKeep t then o else g) P (mrSlot t) q U) *ᵥ ψ with he
  have h1 : F * P * chainOp g q U = F * P * simOp o g g P q q U +
      ∑ i : Fin q, (F * P * simOp o g g P i q U - F * P * simOp o g o P i q U) := by
    rw [chainOp_eq_add_sum_simOp hg, simOp_self, Matrix.mul_add, Finset.mul_sum,
      ← Matrix.mul_assoc (F * P) P, Matrix.mul_assoc F P P, hP]
    simp only [mul_sub]
  have hdec : (F * P * chainOp g q U) *ᵥ ψ =
      e none + ∑ i : Fin q, (e (some (i, false)) - e (some (i, true))) := by
    rw [h1, add_mulVec, sum_mulVec]
    simp only [sub_mulVec, he, mrSlot, mrKeep, Bool.false_eq_true, ite_false, ite_true]
  have hn : nrm ((F * P * chainOp g q U) *ᵥ ψ) ≤ ∑ t, nrm (e t) := by
    rw [hdec, Fintype.sum_option, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    calc nrm (e none + ∑ i : Fin q, (e (some (i, false)) - e (some (i, true))))
        ≤ nrm (e none) + nrm (∑ i : Fin q, (e (some (i, false)) - e (some (i, true)))) :=
          nrm_add_le _ _
      _ ≤ nrm (e none) + ∑ i : Fin q, nrm (e (some (i, false)) - e (some (i, true))) := by
          gcongr; exact nrm_sum_le _ _
      _ ≤ nrm (e none) + ∑ i : Fin q, (nrm (e (some (i, true))) + nrm (e (some (i, false)))) := by
          gcongr with i
          rw [add_comm]
          exact nrm_sub_le _ _
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Option (Fin q × Bool))))
    (f := fun t => nrm (e t))
  rw [Finset.card_univ, card_mrIndex] at hcs
  push_cast at hcs
  calc nrm ((F * P * chainOp g q U) *ᵥ ψ) ^ 2 ≤ (∑ t, nrm (e t)) ^ 2 :=
        pow_le_pow_left₀ (nrm_nonneg _) hn 2
    _ ≤ _ := hcs

end Vector

/-! ## The simulator and the bound for an adversary -/

section Adv

variable {m n w q : ℕ} [NeZero n]

/-- The oracle the simulator applies at the measured query, for the measured
    input `x`: `H` on the slots `some (i, true)`, `H[x ↦ θ]` otherwise. -/
def mrOracleAt (H : Fin m → Fin n) (θ : Fin n) (t : Option (Fin q × Bool)) (x : Fin m) :
    Fin m → Fin n :=
  if mrKeep t then H else Function.update H x θ

/-- The simulator on the slot `t`: the run of `A` against `H` up to `U_i`, the
    measurement of the query register with outcome `x`, then the oracle
    `mrOracleAt H θ t x` at query `i` and `H[x ↦ θ]` at every later query. -/
def simChain (A : QAdv m n w q) (H : Fin m → Fin n) (θ : Fin n) (t : Option (Fin q × Bool)) :
    QComp (m * n * w) (Fin m) :=
  measChain (oracleQ m n w H) (measX m n w) (fun x => oracleQ m n w (Function.update H x θ))
    (fun x => oracleQ m n w (mrOracleAt H θ t x)) (mrSlot t) q A.U

/-- The simulator followed by the adversary's output measurements: the output
    `(x, x', accept)` is the measured input `x`, the query register `x'` of the
    final state and the outcome of the final projector. -/
def simRun (A : QAdv m n w q) (H : Fin m → Fin n) (θ : Fin n) (t : Option (Fin q × Bool)) :
    QComp (m * n * w) (Fin m × Fin m × Bool) :=
  QComp.qbind (simChain A H θ t) fun x => QComp.qbind (measX m n w) fun x' =>
    QComp.qbind A.measure fun acc => QComp.qpure (x, x', acc)

/-- The run of `A` against `G` with its output measurements: the output
    `(x', accept)` is the query register of the final state and the outcome of
    the final projector. -/
def outRun (A : QAdv m n w q) (G : Fin m → Fin n) : QComp (m * n * w) (Fin m × Bool) :=
  QComp.qbind (oracleChain (oracleQ m n w G) q A.U) fun _ => QComp.qbind (measX m n w) fun x' =>
    QComp.qbind A.measure fun acc => QComp.qpure (x', acc)

/-- `Pr[x' = x₀ ∧ accept : A^G]`. -/
def prOutAt (A : QAdv m n w q) (G : Fin m → Fin n) (x₀ : Fin m) : ℝ≥0∞ :=
  prTrue_Q (QComp.qbind (outRun A G) fun o => QComp.qpure (decide (o = (x₀, true)))) A.init

/-- The probability that the simulator on the slot `t` measures `x₀`, the
    adversary's output is `x₀`, and the final projector accepts. -/
def prSimAt (A : QAdv m n w q) (H : Fin m → Fin n) (θ : Fin n) (x₀ : Fin m)
    (t : Option (Fin q × Bool)) : ℝ≥0∞ :=
  prTrue_Q (QComp.qbind (simRun A H θ t) fun o => QComp.qpure (decide (o = (x₀, x₀, true))))
    A.init

/-- The success probability of the simulator with the slot drawn uniformly from
    the `2q + 1` slots. -/
def prMR (A : QAdv m n w q) (H : Fin m → Fin n) (θ : Fin n) (x₀ : Fin m) : ℝ≥0∞ :=
  ((2 * q + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ t, prSimAt A H θ x₀ t

/-- The `(x₀, accept)` branch of `outRun` is conjugation by
    `final * Π_{x₀} * runOp`. -/
theorem outRun_branch (A : QAdv m n w q) (G : Fin m → Fin n) (x₀ : Fin m)
    (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (outRun A G).branch (x₀, true) ρ =
      (A.final * projS m n w {x₀} * runOp A G) * ρ *
        (A.final * projS m n w {x₀} * runOp A G)ᴴ := by
  unfold outRun
  rw [qbind_unit_branch, qbind_branch_of_single _ _ _ x₀, qbind_branch_of_single _ _ _ true]
  · rw [qpure_branch_apply, ite_eq_left rfl]
    unfold oracleQ runOp QAdv.measure
    rw [measProj_branch_true, measX_branch, oracleChain_unitaryChannel_branch]
    simp only [conjTranspose_mul, A.final_conjTranspose, projS_conjTranspose, Matrix.mul_assoc]
  · intro a ha
    apply LinearMap.ext; intro σ
    simp [qpure_branch_apply, Ne.symm ha]
  · intro a ha
    apply LinearMap.ext; intro σ
    simp [qbind_branch_apply, qpure_branch_apply, Ne.symm ha]

/-- The `(x₀, x₀, accept)` branch of `simRun` is conjugation by
    `final * Π_{x₀} * simOp`. -/
theorem simRun_branch (A : QAdv m n w q) (H : Fin m → Fin n) (θ : Fin n) (x₀ : Fin m)
    (t : Option (Fin q × Bool)) (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (simRun A H θ t).branch (x₀, x₀, true) ρ =
      (A.final * projS m n w {x₀} *
          simOp (oracleU m n w H : Matrix _ _ ℂ) (oracleU m n w (Function.update H x₀ θ))
            (oracleU m n w (mrOracleAt H θ t x₀)) (projS m n w {x₀}) (mrSlot t) q A.U) * ρ *
        (A.final * projS m n w {x₀} *
          simOp (oracleU m n w H : Matrix _ _ ℂ) (oracleU m n w (Function.update H x₀ θ))
            (oracleU m n w (mrOracleAt H θ t x₀)) (projS m n w {x₀}) (mrSlot t) q A.U)ᴴ := by
  have hc : ∀ σ, (simChain A H θ t).branch x₀ σ =
      simOp (oracleU m n w H : Matrix _ _ ℂ) (oracleU m n w (Function.update H x₀ θ))
          (oracleU m n w (mrOracleAt H θ t x₀)) (projS m n w {x₀}) (mrSlot t) q A.U * σ *
        (simOp (oracleU m n w H : Matrix _ _ ℂ) (oracleU m n w (Function.update H x₀ θ))
          (oracleU m n w (mrOracleAt H θ t x₀)) (projS m n w {x₀}) (mrSlot t) q A.U)ᴴ :=
    fun σ => measChain_branch (oracleU m n w H) (measX m n w) (fun x => projS m n w {x})
      (measX_branch m n w) (fun x => oracleU m n w (Function.update H x θ))
      (fun x => oracleU m n w (mrOracleAt H θ t x)) (mrSlot t) q A.U x₀ σ
  unfold simRun
  rw [qbind_branch_of_single _ _ _ x₀, qbind_branch_of_single _ _ _ x₀,
    qbind_branch_of_single _ _ _ true]
  · rw [qpure_branch_apply, ite_eq_left rfl, hc]
    unfold QAdv.measure
    rw [measProj_branch_true, measX_branch]
    simp only [conjTranspose_mul, A.final_conjTranspose, projS_conjTranspose, Matrix.mul_assoc]
  · intro a ha
    apply LinearMap.ext; intro σ
    simp [qpure_branch_apply, Ne.symm ha]
  · intro a ha
    apply LinearMap.ext; intro σ
    simp [qbind_branch_apply, qpure_branch_apply, Ne.symm ha]
  · intro a ha
    apply LinearMap.ext; intro σ
    simp [qbind_branch_apply, qpure_branch_apply, Ne.symm ha]

/-- The standard oracle of `H[x₀ ↦ θ]` is `O_H + O_{H[x₀ ↦ θ]} Π_{x₀} − O_H Π_{x₀}`. -/
theorem oracleU_update_eq (H : Fin m → Fin n) (x₀ : Fin m) (θ : Fin n) :
    (oracleU m n w (Function.update H x₀ θ) : Matrix _ _ ℂ) =
      (oracleU m n w H : Matrix _ _ ℂ) +
        (oracleU m n w (Function.update H x₀ θ) : Matrix _ _ ℂ) * projS m n w {x₀} -
        (oracleU m n w H : Matrix _ _ ℂ) * projS m n w {x₀} := by
  have h := oracleU_mul_one_sub_projS (w := w) (Function.update H x₀ θ) H {x₀}
    (fun x hx => Function.update_of_ne (by simpa using hx : x ≠ x₀) θ H)
  rw [mul_sub, mul_sub, mul_one, mul_one] at h
  rw [← sub_eq_zero] at h ⊢
  rw [← h]
  abel

/-- The probability of an output branch conjugated by `Y` at the initial state
    `∑ₖ ψₖ ψₖ†` is the sum of the squared norms of `Y ψₖ`. -/
theorem prTrue_Q_eq_sum_nrm_sq {d : ℕ} (I : QComp d Bool) (ρ₀ : DensityMatrix d)
    (Y : Matrix (Fin d) (Fin d) ℂ) (hI : ∀ σ, I.branch true σ = Y * σ * Yᴴ)
    {ι : Type} [Fintype ι] (ψ : ι → Fin d → ℂ) (hρ : ρ₀.val = ∑ k, vecMulVec (ψ k) (star (ψ k))) :
    prTrue_Q I ρ₀ = ENNReal.ofReal (∑ k, nrm (Y *ᵥ ψ k) ^ 2) := by
  unfold prTrue_Q
  rw [hI, hρ, trace_mul_sum_vecMulVec_mul_conjTranspose, Complex.ofReal_re]

/-- Measure-and-reprogram (Don–Fehr–Majenz–Schaffner, CRYPTO 2019, Theorem 2,
    single reprogrammed point): for every `q`-query adversary `A`, oracle `H`,
    point `x₀` and value `θ`, the simulator with a uniform slot among the
    `2q + 1` slots measures `x₀`, and the adversary run against the reprogrammed
    oracle outputs `x₀` and accepts, with probability at least
    `Pr[x' = x₀ ∧ accept : A^{H[x₀ ↦ θ]}] / (2q + 1)²`. -/
theorem measure_reprogram (A : QAdv m n w q) (H : Fin m → Fin n) (x₀ : Fin m) (θ : Fin n) :
    prOutAt A (Function.update H x₀ θ) x₀ / ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 ≤ prMR A H θ x₀ := by
  obtain ⟨ψ, hρ⟩ := exists_eq_sum_vecMulVec_of_posSemidef A.init.psd
  set P := projS m n w {x₀} with hP
  set o : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ :=
    (oracleU m n w H : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) with ho
  set g : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ :=
    (oracleU m n w (Function.update H x₀ θ) : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ)
    with hgdef
  have hg : g = o + g * P - o * P := oracleU_update_eq H x₀ θ
  set e : Option (Fin q × Bool) → Fin (m * n * w) → Fin (m * n * w) → ℂ := fun t k =>
    (A.final * P * simOp o g (if mrKeep t then o else g) P (mrSlot t) q A.U) *ᵥ ψ k with he
  have hout : prOutAt A (Function.update H x₀ θ) x₀ =
      ENNReal.ofReal (∑ k, nrm ((A.final * P * chainOp g q A.U) *ᵥ ψ k) ^ 2) := by
    refine prTrue_Q_eq_sum_nrm_sq _ _ _ (fun σ => ?_) ψ hρ
    rw [qbind_decide_eq_branch_true, outRun_branch]
    rfl
  have hr : ∀ t : Option (Fin q × Bool),
      (oracleU m n w (mrOracleAt H θ t x₀) : Matrix _ _ ℂ) = if mrKeep t then o else g := by
    intro t
    unfold mrOracleAt
    split_ifs <;> rfl
  have hsim : ∀ t, prSimAt A H θ x₀ t = ENNReal.ofReal (∑ k, nrm (e t k) ^ 2) := by
    intro t
    refine prTrue_Q_eq_sum_nrm_sq _ _ _ (fun σ => ?_) ψ hρ
    rw [qbind_decide_eq_branch_true, simRun_branch, hr]
  have hvec : ∀ k, nrm ((A.final * P * chainOp g q A.U) *ᵥ ψ k) ^ 2 ≤
      (2 * q + 1 : ℝ) * ∑ t, nrm (e t k) ^ 2 := fun k =>
    nrm_sq_le_card_mul_sum_simOp hg (projS_mul_self m n w {x₀}) q A.U (ψ k)
  have hreal : ∑ k, nrm ((A.final * P * chainOp g q A.U) *ᵥ ψ k) ^ 2 ≤
      (2 * q + 1 : ℝ) * ∑ t, ∑ k, nrm (e t k) ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hvec k
  have hle : prOutAt A (Function.update H x₀ θ) x₀ ≤
      ((2 * q + 1 : ℕ) : ℝ≥0∞) * ∑ t, prSimAt A H θ x₀ t := by
    rw [hout]
    simp only [hsim]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => Finset.sum_nonneg fun k _ => sq_nonneg _),
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    exact hreal
  have hN0 : ((2 * q + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (2 * q).succ_ne_zero
  have hNt : ((2 * q + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine ENNReal.div_le_of_le_mul ?_
  calc prOutAt A (Function.update H x₀ θ) x₀
      ≤ ((2 * q + 1 : ℕ) : ℝ≥0∞) * ∑ t, prSimAt A H θ x₀ t := hle
    _ = prMR A H θ x₀ * ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 := by
      unfold prMR
      rw [sq, ← mul_assoc, mul_comm _ (((2 * q + 1 : ℕ) : ℝ≥0∞)), ← mul_assoc, ← mul_assoc,
        ENNReal.mul_inv_cancel hN0 hNt, one_mul, mul_comm]

/-- The probability that the simulator on the slot `t` measures `x₀` and the
    final projector accepts, with the adversary's output `x'` discarded. -/
def prSimAcc (A : QAdv m n w q) (H : Fin m → Fin n) (θ : Fin n) (x₀ : Fin m)
    (t : Option (Fin q × Bool)) : ℝ≥0∞ :=
  prTrue_Q (QComp.qbind (simRun A H θ t) fun o => QComp.qpure (decide (o.1 = x₀) && o.2.2))
    A.init

/-- Discarding the adversary's output `x'` does not decrease the simulator's
    success probability. -/
theorem prSimAt_le_prSimAcc (A : QAdv m n w q) (H : Fin m → Fin n) (θ : Fin n) (x₀ : Fin m)
    (t : Option (Fin q × Bool)) : prSimAt A H θ x₀ t ≤ prSimAcc A H θ x₀ t := by
  unfold prSimAt prSimAcc prTrue_Q
  apply ENNReal.ofReal_le_ofReal
  rw [qbind_decide_eq_branch_true, qbind_branch_apply, tsum_fintype, Matrix.trace_sum,
    Complex.re_sum]
  have hnn : ∀ o, 0 ≤ ((simRun A H θ t).branch o A.init.val).trace.re := fun o =>
    (Complex.le_def.mp ((simRun A H θ t).branch_psd o _ A.init.psd).trace_nonneg).1
  refine le_trans ?_ (Finset.single_le_sum (f := fun o =>
    ((QComp.qpure (decide (o.1 = x₀) && o.2.2) : QComp (m * n * w) Bool).branch true
      ((simRun A H θ t).branch o A.init.val)).trace.re) (fun o _ => ?_)
    (Finset.mem_univ (x₀, x₀, true)))
  · simp [qpure_branch_apply]
  · simp only [qpure_branch_apply]
    split_ifs
    · exact hnn o
    · simp

/-- Measure-and-reprogram with the adversary's output `x'` discarded by the
    simulator: `Pr[x' = x₀ ∧ accept : A^{H[x₀ ↦ θ]}] / (2q + 1)²` is at most the
    probability, over a uniform slot, that the simulator measures `x₀` and the
    final projector accepts. -/
theorem measure_reprogram_acc (A : QAdv m n w q) (H : Fin m → Fin n) (x₀ : Fin m) (θ : Fin n) :
    prOutAt A (Function.update H x₀ θ) x₀ / ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 ≤
      ((2 * q + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ t, prSimAcc A H θ x₀ t :=
  (measure_reprogram A H x₀ θ).trans
    (mul_le_mul_right (Finset.sum_le_sum fun t _ => prSimAt_le_prSimAcc A H θ x₀ t) _)

end Adv

end CatCrypt.Quantum.QROM
