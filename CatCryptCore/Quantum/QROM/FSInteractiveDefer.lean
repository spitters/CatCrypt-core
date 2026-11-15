/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.FiatShamir
public import CatCryptCore.Quantum.QROM.MultiRound
public import CatCryptCore.Quantum.QROM.QSearch

/-!
# The interactive Fiat–Shamir game as an adversary without oracle access

The interactive game `fsInteractive A V H` measures the commitment `x` in the middle of the
run of `A`, continues against the reprogrammed oracle `H[x ↦ θ]`, measures the query register
and tests the verifier projector `V(x, θ)`. For a fixed slot `t` and a fixed challenge `θ`,
deferred measurement turns this program into a `0`-query adversary `fsDefer A V H t θ` on the
work register extended by two ancillas `Fin m`: the prefix unitary of the run, the record of
the commitment into the first ancilla followed by the suffix unitary `fsSufU A H t x θ`
controlled on it, the record of the final query register into the second ancilla, and the
final projector `∑ x, V(x, θ) ⊗ |x⟩⟨x| ⊗ 1`.

## Main definitions

* `preU o j q U` — the unitary `U_j o ⋯ o U_0` before the instrument of `measChain`
* `measXRound m n w ans` — the measurement of the query register as a classical round with
  answer unitaries `ans x`
* `verProj V θ` — the projector `∑ x, V(x, θ) ⊗ |x⟩⟨x|` on the register with one ancilla
* `fsDeferU A H t θ`, `fsDefer A V H t θ` — the deferred unitary and the `0`-query adversary

## Main results

* `simOp_eq_sufU_mul_preU` — the Kraus operator of `measChain` with unitary oracles is the
  suffix unitary, the projector and the prefix unitary
* `trace_sum_kr_ancProj_mul_roundV` — the deferred-measurement identity for one ancilla and
  an observable controlled on it
* `prOut0_fsDefer` — `prOut0 (fsDefer A V H t θ)` is the acceptance probability of the
  interactive game on the slot `t` with the challenge `θ`
* `prTrue_fsInteractive_eq_sum_prOut0_fsDefer` — the acceptance probability of
  `fsInteractive A V H` is the average of `prOut0 (fsDefer A V H t θ)` over uniform coins
  `(t, θ)`, in the coin form of `qSearchAdv`

## References

* [Nielsen, Chuang — Quantum Computation and Quantum Information], §4.4, the deferred
  measurement principle
* [Don, Fehr, Majenz, Schaffner — Security of the Fiat-Shamir Transformation in the Quantum
  Random-Oracle Model, CRYPTO 2019]
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
  CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The Kraus operator of `measChain` split at the instrument -/

section Factor

variable {d : ℕ}

/-- The unitary `U_j o ⋯ o U_0` of `measChain` before its instrument, `U_q o ⋯ o U_0` when
    `j ≥ q`. -/
def preU (o : Matrix.unitaryGroup (Fin d) ℂ) :
    (j q : ℕ) → (Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) → Matrix.unitaryGroup (Fin d) ℂ
  | 0, _, U => U 0
  | _ + 1, 0, U => U 0
  | j + 1, q + 1, U => preU o j q (Fin.tail U) * o * U 0

/-- The value of `chainU` is the chain operator of the oracle unitary. -/
theorem chainU_val (g : Matrix.unitaryGroup (Fin d) ℂ) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    (chainU g q U : Matrix (Fin d) (Fin d) ℂ) = chainOp (g : Matrix (Fin d) (Fin d) ℂ) q U := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [chainU, chainOp, Submonoid.coe_mul, ih]

/-- The Kraus operator `simOp` of `measChain` with unitary oracles is the suffix unitary
    `sufU g r j q U`, the projector `P` and the prefix unitary `preU o j q U`. -/
theorem simOp_eq_sufU_mul_preU (o g r : Matrix.unitaryGroup (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) :
    ∀ (j q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      simOp (o : Matrix (Fin d) (Fin d) ℂ) g r P j q U =
        (sufU g r j q U : Matrix (Fin d) (Fin d) ℂ) * P * preU o j q U
  | 0, 0, U => by simp [simOp, sufU, preU]
  | 0, q + 1, U => by simp only [simOp, sufU, preU, Submonoid.coe_mul, chainU_val]
  | _ + 1, 0, U => by simp [simOp, sufU, preU]
  | j + 1, q + 1, U => by
    rw [simOp, simOp_eq_sufU_mul_preU o g r P j q (Fin.tail U)]
    simp only [sufU, preU, Submonoid.coe_mul, Matrix.mul_assoc]

end Factor

/-! ## Deferred measurement with an observable controlled on the ancilla -/

section Defer

variable {d c a d' : ℕ}

/-- The lifted unitary `U ⊗ 1` conjugates `σ ⊗ E` to `U σ Uᴴ ⊗ E`. -/
theorem liftU_mul_kr_mul_conjTranspose (e : Fin (d * c) ≃ Fin d')
    (U : Matrix.unitaryGroup (Fin d) ℂ) (σ : Matrix (Fin d) (Fin d) ℂ)
    (E : Matrix (Fin c) (Fin c) ℂ) :
    (liftU e U : Matrix (Fin d') (Fin d') ℂ) * kr e σ E *
        (liftU e U : Matrix (Fin d') (Fin d') ℂ)ᴴ =
      kr e ((U : Matrix (Fin d) (Fin d) ℂ) * σ * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) E := by
  rw [liftU_val, kr_mul, kr_conjTranspose, kr_mul, conjTranspose_one, one_mul, mul_one]

/-- `tr ((A ⊗ |z⟩⟨z|) (B ⊗ |y⟩⟨y'|))` is `tr (A B)` when `z = y = y'` and `0` otherwise. -/
theorem trace_kr_ancProj_mul_kr_ancUnit (e : Fin (d * c) ≃ Fin d')
    (A B : Matrix (Fin d) (Fin d) ℂ) (z y y' : Fin c) :
    (kr e A (ancProj z) * kr e B (ancUnit y y')).trace =
      if z = y ∧ y = y' then (A * B).trace else 0 := by
  rw [kr_mul, trace_kr, ancProj_mul_ancUnit]
  by_cases hz : z = y
  · subst hz
    by_cases hy : z = y' <;> simp [hy, trace_ancUnit]
  · simp [hz]

variable [NeZero c]

/-- Deferred measurement of one classical round against an observable controlled on the
    ancilla: on `σ ⊗ |0⟩⟨0|`, the prefix unitary `Pre ⊗ 1` and the deferred round `roundV`,
    the observable `∑ z, X z ⊗ |z⟩⟨z|` has the expectation `∑ y, tr (X y K_y Pre σ Preᴴ K_yᴴ)`
    with `K_y = ans (f y) P y`. -/
theorem trace_sum_kr_ancProj_mul_roundV (e : Fin (d * c) ≃ Fin d') (R : ClassicalRound d c a)
    (f : Fin c → Fin a) (Pre : Matrix.unitaryGroup (Fin d) ℂ)
    (X : Fin c → Matrix (Fin d) (Fin d) ℂ) (σ : Matrix (Fin d) (Fin d) ℂ) :
    ((∑ z, kr e (X z) (ancProj z)) *
        (((roundV e R f * liftU e Pre : Matrix.unitaryGroup (Fin d') ℂ) :
            Matrix (Fin d') (Fin d') ℂ) * kr e σ (ancProj 0) *
          ((roundV e R f * liftU e Pre : Matrix.unitaryGroup (Fin d') ℂ) :
            Matrix (Fin d') (Fin d') ℂ)ᴴ)).trace =
      ∑ y, (X y * (((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y) *
        ((Pre : Matrix (Fin d) (Fin d) ℂ) * σ * (Pre : Matrix (Fin d) (Fin d) ℂ)ᴴ) *
        ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y)ᴴ)).trace := by
  have h1 : ((roundV e R f * liftU e Pre : Matrix.unitaryGroup (Fin d') ℂ) :
        Matrix (Fin d') (Fin d') ℂ) * kr e σ (ancProj 0) *
        ((roundV e R f * liftU e Pre : Matrix.unitaryGroup (Fin d') ℂ) :
          Matrix (Fin d') (Fin d') ℂ)ᴴ =
      (roundV e R f : Matrix (Fin d') (Fin d') ℂ) *
        kr e ((Pre : Matrix (Fin d) (Fin d) ℂ) * σ * (Pre : Matrix (Fin d) (Fin d) ℂ)ᴴ)
          (ancProj 0) * (roundV e R f : Matrix (Fin d') (Fin d') ℂ)ᴴ := by
    rw [← liftU_mul_kr_mul_conjTranspose, Submonoid.coe_mul, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [h1, roundV_mul_kr_ancProj_zero, Finset.sum_mul, trace_sum]
  simp only [Finset.mul_sum, trace_sum, trace_kr_ancProj_mul_kr_ancUnit]
  simp [ite_and]

end Defer

/-! ## The deferred interactive game -/

section Game

variable (m n w : ℕ)

/-- Distinct singleton projectors of the query register are orthogonal. -/
theorem projS_singleton_mul_of_ne {x y : Fin m} (h : x ≠ y) :
    projS m n w {x} * projS m n w {y} = 0 := by
  rw [projS_eq_diagonal, projS_eq_diagonal, diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [diagonal_apply_eq, indS, Finset.mem_singleton, Matrix.zero_apply]
    grind
  · simp [hij]

/-- The measurement of the query register as a classical round with the answer unitary
    `ans x` on the outcome `x`. -/
def measXRound (ans : Fin m → Matrix.unitaryGroup (Fin (m * n * w)) ℂ) :
    ClassicalRound (m * n * w) m m where
  P x := projS m n w {x}
  P_conjTranspose x := projS_conjTranspose m n w {x}
  P_mul_self x := projS_mul_self m n w {x}
  P_orth _ _ h := projS_singleton_mul_of_ne m n w h
  P_sum := sum_projS_singleton m n w
  ans := ans

variable {m n w} {q : ℕ} [NeZero m] [NeZero n]

/-- The verifier projector controlled on the commitment ancilla:
    `∑ x, V(x, θ) ⊗ |x⟩⟨x|`. -/
def verProj (V : QVerifier m n w) (θ : Fin n) :
    Matrix (Fin (m * n * (w * m))) (Fin (m * n * (w * m))) ℂ :=
  ∑ x, kr (ancE m n w m) (V.proj x θ) (ancProj x)

omit [NeZero m] [NeZero n] in
theorem verProj_conjTranspose (V : QVerifier m n w) (θ : Fin n) :
    (verProj V θ)ᴴ = verProj V θ := by
  simp only [verProj, conjTranspose_sum, kr_conjTranspose, V.proj_conjTranspose,
    ancProj_conjTranspose]

omit [NeZero m] [NeZero n] in
theorem verProj_mul_self (V : QVerifier m n w) (θ : Fin n) :
    verProj V θ * verProj V θ = verProj V θ := by
  unfold verProj
  rw [Finset.sum_mul_sum]
  simp only [kr_mul, ancProj_mul_ancProj]
  simp [apply_ite, kr_zero_right, V.proj_mul_self, Finset.sum_ite_eq]

/-- The deferred unitary of the interactive game on the slot `t` with the challenge `θ`: the
    prefix unitary of the run of `A` against `H`, the record of the commitment `x` into the
    first ancilla and `fsSufU A H t x θ` controlled on it, then the record of the query register
    into the second ancilla. -/
def fsDeferU (A : QAdv m n w q) (H : Fin m → Fin n) (t : Option (Fin q × Bool)) (θ : Fin n) :
    Matrix.unitaryGroup (Fin (m * n * (w * m * m))) ℂ :=
  roundV (ancE m n (w * m) m) (measXRound m n (w * m) fun _ => 1) id *
    liftU (ancE m n (w * m) m)
      (roundV (ancE m n w m) (measXRound m n w fun x => fsSufU A H t x θ) id *
        liftU (ancE m n w m) (preU (oracleU m n w H) (mrSlot t) q A.U))

/-- The interactive game on the slot `t` with the challenge `θ` as a `0`-query adversary on
    the register with two ancillas: the initial state `A.init ⊗ |0⟩⟨0| ⊗ |0⟩⟨0|`, the unitary
    `fsDeferU A H t θ` and the final projector `∑ x, V(x, θ) ⊗ |x⟩⟨x| ⊗ 1`. -/
def fsDefer (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n)
    (t : Option (Fin q × Bool)) (θ : Fin n) : QAdv m n (w * m * m) 0 where
  U _ := fsDeferU A H t θ
  init := liftInit (c := m) (liftInit (c := m) A.init)
  final := kr (ancE m n (w * m) m) (verProj V θ) 1
  final_conjTranspose := by rw [kr_conjTranspose, verProj_conjTranspose, conjTranspose_one]
  final_mul_self := by rw [kr_mul, verProj_mul_self, one_mul]

omit [NeZero m] [NeZero n] in
/-- The verifier projector after the measurement of the query register `y`, moved onto the
    state: `tr (Y Π'_y M Π'_y) = tr ((∑ x, Π_y V(x, θ) Π_y ⊗ |x⟩⟨x|) M)`. -/
theorem trace_verProj_mul_projS (V : QVerifier m n w) (θ : Fin n) (y : Fin m)
    (M : Matrix (Fin (m * n * (w * m))) (Fin (m * n * (w * m))) ℂ) :
    (verProj V θ * (projS m n (w * m) {y} * M * (projS m n (w * m) {y})ᴴ)).trace =
      ((∑ x, kr (ancE m n w m) (projS m n w {y} * V.proj x θ * projS m n w {y}) (ancProj x)) *
        M).trace := by
  rw [projS_conjTranspose, projS_lift]
  have hc : (verProj V θ * (kr (ancE m n w m) (projS m n w {y}) 1 * M *
      kr (ancE m n w m) (projS m n w {y}) 1)).trace =
      (kr (ancE m n w m) (projS m n w {y}) 1 * verProj V θ *
        kr (ancE m n w m) (projS m n w {y}) 1 * M).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hc]
  unfold verProj
  simp only [Finset.mul_sum, Finset.sum_mul, kr_mul, one_mul, mul_one]

/-- The trace of the accepting branch of the deferred adversary is the sum over the
    commitment `x` and the measured query register `y` of `tr (V(x, θ) Π_y N_x Π_y)`, with
    `N_x = K_x Pre ρ Preᴴ K_xᴴ` and `K_x = fsSufU A H t x θ Π_x`. -/
theorem trace_fsDefer (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n)
    (t : Option (Fin q × Bool)) (θ : Fin n) :
    (((fsDefer A V H t θ).final * (fsDeferU A H t θ : Matrix _ _ ℂ)) *
        (fsDefer A V H t θ).init.val *
        ((fsDefer A V H t θ).final * (fsDeferU A H t θ : Matrix _ _ ℂ))ᴴ).trace =
      ∑ x, ∑ y, (V.proj x θ * (projS m n w {y} *
        (((fsSufU A H t x θ : Matrix _ _ ℂ) * projS m n w {x}) *
          ((preU (oracleU m n w H) (mrSlot t) q A.U : Matrix _ _ ℂ) * A.init.val *
            (preU (oracleU m n w H) (mrSlot t) q A.U : Matrix _ _ ℂ)ᴴ) *
          ((fsSufU A H t x θ : Matrix _ _ ℂ) * projS m n w {x})ᴴ) *
        projS m n w {y})).trace := by
  have hF : (fsDefer A V H t θ).final =
      ∑ z, kr (ancE m n (w * m) m) (verProj V θ) (ancProj z) := by
    rw [← kr_sum_right, sum_ancProj]
    rfl
  have h0 : (((fsDefer A V H t θ).final * (fsDeferU A H t θ : Matrix _ _ ℂ)) *
        (fsDefer A V H t θ).init.val *
        ((fsDefer A V H t θ).final * (fsDeferU A H t θ : Matrix _ _ ℂ))ᴴ).trace =
      ((fsDefer A V H t θ).final * ((fsDeferU A H t θ : Matrix _ _ ℂ) *
        (fsDefer A V H t θ).init.val * (fsDeferU A H t θ : Matrix _ _ ℂ)ᴴ)).trace := by
    rw [conjTranspose_mul, (fsDefer A V H t θ).final_conjTranspose, ← trace_proj_mul_mul_proj
      (fsDefer A V H t θ).final_mul_self]
    simp only [Matrix.mul_assoc]
  rw [h0, hF]
  refine (trace_sum_kr_ancProj_mul_roundV (ancE m n (w * m) m) (measXRound m n (w * m) fun _ => 1)
    id _ (fun _ => verProj V θ) (liftInit (c := m) A.init).val).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [measXRound, id, OneMemClass.coe_one, one_mul]
  rw [trace_verProj_mul_projS]
  refine (trace_sum_kr_ancProj_mul_roundV (ancE m n w m)
    (measXRound m n w fun x => fsSufU A H t x θ) id _
    (fun x => projS m n w {y} * V.proj x θ * projS m n w {y}) A.init.val).trans ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [measXRound, id]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

omit [NeZero m] in
/-- The trace of the accepting branch of the interactive game on the slot `t` with the
    challenge `θ`, in the form of `trace_fsDefer`. -/
theorem trace_simChain_branch (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n)
    (t : Option (Fin q × Bool)) (θ : Fin n) :
    ((QComp.qbind (simChain A H θ t) fun x =>
        QComp.qbind (measX m n w) fun _ => (A.withVerifier V x θ).measure).branch true
          A.init.val).trace =
      ∑ x, ∑ y, (V.proj x θ * (projS m n w {y} *
        (((fsSufU A H t x θ : Matrix _ _ ℂ) * projS m n w {x}) *
          ((preU (oracleU m n w H) (mrSlot t) q A.U : Matrix _ _ ℂ) * A.init.val *
            (preU (oracleU m n w H) (mrSlot t) q A.U : Matrix _ _ ℂ)ᴴ) *
          ((fsSufU A H t x θ : Matrix _ _ ℂ) * projS m n w {x})ᴴ) *
        projS m n w {y})).trace := by
  rw [qbind_branch_apply, tsum_fintype, trace_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [qbind_branch_apply, tsum_fintype, trace_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hS := measChain_branch (oracleU m n w H) (measX m n w) (fun x => projS m n w {x})
    (measX_branch m n w) (fun x' => oracleU m n w (Function.update H x' θ))
    (fun x' => oracleU m n w (mrOracleAt H θ t x')) (mrSlot t) q A.U x A.init.val
  simp only [simChain, oracleQ]
  rw [hS, simOp_eq_sufU_mul_preU]
  simp only [QAdv.measure, QAdv.withVerifier, measProj_branch_true, measX_branch,
    V.proj_conjTranspose, projS_conjTranspose, trace_proj_mul_mul_proj (V.proj_mul_self x θ)]
  simp only [fsSufU, conjTranspose_mul, Matrix.mul_assoc]

/-- The acceptance probability of the deferred adversary is the acceptance probability of the
    interactive game on the slot `t` with the challenge `θ`. -/
theorem prOut0_fsDefer (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n)
    (t : Option (Fin q × Bool)) (θ : Fin n) :
    prOut0 (fsDefer A V H t θ) =
      prTrue_Q (QComp.qbind (simChain A H θ t) fun x =>
        QComp.qbind (measX m n w) fun _ => (A.withVerifier V x θ).measure) A.init := by
  unfold prOut0 prOut prTrue_Q
  rw [run_branch_true, runOp_zero, trace_simChain_branch]
  exact congrArg (fun z : ℂ => ENNReal.ofReal z.re) (trace_fsDefer A V H t θ)

/-- The acceptance probability of the interactive game is the average of the acceptance
    probabilities of the deferred adversaries over uniform coins `(t, θ)`. -/
theorem prTrue_fsInteractive_eq_sum_prOut0_fsDefer (A : QAdv m n w q) (V : QVerifier m n w)
    (H : Fin m → Fin n) :
    prTrue_Q (fsInteractive A V H) A.init =
      ∑ i : Option (Fin q × Bool) × Fin n,
        (Fintype.card (Option (Fin q × Bool) × Fin n) : ℝ≥0∞)⁻¹ *
          prOut0 (fsDefer A V H i.1 i.2) := by
  rw [sum_prod_uniform, fsInteractive_eq_simChain, prTrue_Q_uniformQ_bind]
  simp only [prTrue_Q_uniformQ_bind, prOut0_fsDefer, Finset.mul_sum]

end Game

end CatCrypt.Quantum.QROM
