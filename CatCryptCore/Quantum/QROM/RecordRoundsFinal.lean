/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.RecordRounds
public import CatCryptCore.Quantum.QROM.RoundOracleLocal

/-!
# Diagonal final tests of the recorded run

Three facts about the final test of a flattened multi-round adversary, read from the basis
states of its register.

* Additivity: the acceptance probability with the diagonal test `G` is the sum of those with
  the tests `G ∧ b` and `G ∧ ¬b`, for the flattened adversary `(toQAdv A f).withFinalB G` and
  for the recorded adversary `recordGen A G`.
* Weighted tests: the value `prOutW B v H` of the diagonal observable `∑ i, v i • |i⟩⟨i|` on
  the state before the final measurement is linear and monotone in the weight `v`, and at the
  indicator of `G` it is the acceptance probability of `B.withFinalB G`.
* Avoiding a set of outcomes: if the test `G` holds only at basis states whose recorded round
  outcomes all lie outside `Y`, the acceptance probability of `recordGen A G` is the
  probability `prOutAvoidMRGen` that the run accepts and no round outcome lies in `Y`.

## Main definitions

* `diagW v` — the diagonal observable of a real weight `v`
* `QAdv.outState B H` — the state of the run of `B` against `H` before its final measurement
* `prOutW B v H` — the value of `diagW v` on that state
* `CommCompress Q C` — the branch of `C` commutes with the compression `σ ↦ Q σ Q`

## Main results

* `prOut_withFinalB_add`, `prOutMRGen_recordGen_add` — additivity over a split of the test
* `prOutW_sum`, `prOutW_mono`, `prOut_withFinalB_eq_prOutW` — the weighted test
* `prOutMRGen_recordGen_eq_prOutAvoidMRGen` — a test that requires every recorded round outcome
  to lie outside `Y` sees only the branches whose round outcomes avoid `Y`

## The argument for the last result

Round `0` of the recorded run writes its outcome `y` into the digit of its ancilla, so the part
of the state after round `0` with `y ∈ Y` is supported on the basis states with that digit in
`Y`: it is invariant under the compression by the diagonal projector `Q` onto those states.
Every later operation is block diagonal along the digit, so it commutes with the compression,
and the final test `diagB G` is orthogonal to `Q`. The part with `y ∉ Y` is the induction
hypothesis for the later rounds.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.UnitaryChannel

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Weighted diagonal observables -/

section Weighted

variable {d : ℕ}

/-- The diagonal observable `∑ i, v i • |i⟩⟨i|` of a real weight `v`. -/
def diagW (v : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => (v i : ℂ)

theorem trace_diagW_mul_re (v : Fin d → ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (diagW v * ρ).trace.re = ∑ i, v i * (ρ i i).re := by
  simp [diagW, Matrix.trace, Matrix.diagonal_mul]

/-- The diagonal projector of `G` is the diagonal observable of the indicator of `G`. -/
theorem diagB_eq_diagW (G : Fin d → Bool) : diagB G = diagW fun i => if G i then 1 else 0 := by
  unfold diagB diagW
  congr 1
  funext i
  split_ifs <;> simp_all

theorem trace_diagW_sum_re {ι : Type} (s : Finset ι) (p : ι → ℝ) (u : ι → Fin d → ℝ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (diagW (∑ t ∈ s, p t • u t) * ρ).trace.re = ∑ t ∈ s, p t * (diagW (u t) * ρ).trace.re := by
  simp only [trace_diagW_mul_re, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem trace_diagW_add_re (u v : Fin d → ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (diagW (u + v) * ρ).trace.re = (diagW u * ρ).trace.re + (diagW v * ρ).trace.re := by
  simp only [trace_diagW_mul_re, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem trace_diagW_mono_re {u v : Fin d → ℝ} (huv : u ≤ v) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) : (diagW u * ρ).trace.re ≤ (diagW v * ρ).trace.re := by
  rw [trace_diagW_mul_re, trace_diagW_mul_re]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (huv i) ?_
  exact (Complex.nonneg_iff.mp (hρ.diag_nonneg (i := i))).1

theorem trace_diagW_nonneg_re {v : Fin d → ℝ} (hv : 0 ≤ v) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) : 0 ≤ (diagW v * ρ).trace.re := by
  have h := trace_diagW_mono_re hv hρ
  simpa [diagW] using h

end Weighted

/-! ## The weighted test of a single-run adversary -/

section Single

variable {m n w q : ℕ} [NeZero n]

/-- The state of the run of `B` against `H` before its final measurement. -/
def QAdv.outState (B : QAdv m n w q) (H : Fin m → Fin n) :
    Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ :=
  (scChain (scOracleQ m n w H ∅) q B.U).branch false B.init.val

theorem QAdv.outState_posSemidef (B : QAdv m n w q) (H : Fin m → Fin n) :
    (B.outState H).PosSemidef :=
  (scChain (scOracleQ m n w H ∅) q B.U).branch_psd false _ B.init.psd

/-- The value of the weighted diagonal test `diagW v` on the state of `B` before its final
    measurement. -/
def prOutW (B : QAdv m n w q) (v : Fin (m * n * w) → ℝ) (H : Fin m → Fin n) : ℝ :=
  (diagW v * B.outState H).trace.re

/-- The acceptance probability of the diagonal test `G` is the weighted test at the indicator
    of `G`. -/
theorem prOut_withFinalB_eq_prOutW (B : QAdv m n w q) (G : Fin (m * n * w) → Bool)
    (H : Fin m → Fin n) :
    prOut (B.withFinalB G) H = ENNReal.ofReal (prOutW B (fun i => if G i then 1 else 0) H) := by
  rw [prOut_eq_trace_scChain_empty, prOutW, ← diagB_eq_diagW]
  rfl

theorem prOutW_sum {ι : Type} (B : QAdv m n w q) (s : Finset ι) (p : ι → ℝ)
    (u : ι → Fin (m * n * w) → ℝ) (H : Fin m → Fin n) :
    prOutW B (∑ t ∈ s, p t • u t) H = ∑ t ∈ s, p t * prOutW B (u t) H :=
  trace_diagW_sum_re s p u _

theorem prOutW_add (B : QAdv m n w q) (u v : Fin (m * n * w) → ℝ) (H : Fin m → Fin n) :
    prOutW B (u + v) H = prOutW B u H + prOutW B v H :=
  trace_diagW_add_re u v _

/-- A pointwise bound on the weights bounds the weighted tests. -/
theorem prOutW_mono (B : QAdv m n w q) {u v : Fin (m * n * w) → ℝ} (huv : u ≤ v)
    (H : Fin m → Fin n) : prOutW B u H ≤ prOutW B v H :=
  trace_diagW_mono_re huv (B.outState_posSemidef H)

theorem prOutW_nonneg (B : QAdv m n w q) {v : Fin (m * n * w) → ℝ} (hv : 0 ≤ v)
    (H : Fin m → Fin n) : 0 ≤ prOutW B v H :=
  trace_diagW_nonneg_re hv (B.outState_posSemidef H)

/-- Additivity of the acceptance probability over the split of a diagonal test by `b`. -/
theorem prOut_withFinalB_add (B : QAdv m n w q) (G b : Fin (m * n * w) → Bool)
    (H : Fin m → Fin n) :
    prOut (B.withFinalB G) H = prOut (B.withFinalB fun i => G i && b i) H +
      prOut (B.withFinalB fun i => G i && !b i) H := by
  rw [prOut_withFinalB_eq_prOutW, prOut_withFinalB_eq_prOutW, prOut_withFinalB_eq_prOutW,
    ← ENNReal.ofReal_add (prOutW_nonneg B (fun i => by dsimp only; split_ifs <;> simp) H)
      (prOutW_nonneg B (fun i => by dsimp only; split_ifs <;> simp) H), ← prOutW_add]
  congr 2
  funext i
  cases hGi : G i <;> cases hbi : b i <;> simp [hGi, hbi]

end Single

/-! ## Additivity for the recorded adversary -/

section RecordAdd

variable {m n w q k c a : ℕ} [NeZero c] [NeZero n]

/-- Additivity of the acceptance probability of the recorded adversary over the split of its
    final test by `b`. -/
theorem prOutMRGen_recordGen_add (A : QAdvMR m n w q k c a) (f : Fin c → Fin a)
    (G b : Fin (m * n * ancW c k w) → Bool) (H : Fin m → Fin n) :
    prOutMRGen (recordGen A G) H f = prOutMRGen (recordGen A fun i => G i && b i) H f +
      prOutMRGen (recordGen A fun i => G i && !b i) H f := by
  rw [← prOut_withFinalB_toQAdv_eq, ← prOut_withFinalB_toQAdv_eq, ← prOut_withFinalB_toQAdv_eq]
  exact prOut_withFinalB_add _ G b H

end RecordAdd

/-! ## Compressions commuting with a chain -/

section Compress

variable {d c a : ℕ}

/-- The branch of `C` commutes with the compression `σ ↦ Q σ Q`. -/
def CommCompress (Q : Matrix (Fin d) (Fin d) ℂ) (C : QComp d Unit) : Prop :=
  ∀ σ, C.branch () (Q * σ * Q) = Q * C.branch () σ * Q

theorem conj_compress {Q K : Matrix (Fin d) (Fin d) ℂ} (hQ : Qᴴ = Q) (hK : K * Q = Q * K)
    (σ : Matrix (Fin d) (Fin d) ℂ) : K * (Q * σ * Q) * Kᴴ = Q * (K * σ * Kᴴ) * Q := by
  have hK' : Kᴴ * Q = Q * Kᴴ := by
    have h := congrArg conjTranspose hK
    rw [conjTranspose_mul, conjTranspose_mul, hQ] at h
    exact h.symm
  calc K * (Q * σ * Q) * Kᴴ = (K * Q) * σ * (Q * Kᴴ) := by simp only [Matrix.mul_assoc]
    _ = (Q * K) * σ * (Kᴴ * Q) := by rw [hK, hK']
    _ = Q * (K * σ * Kᴴ) * Q := by simp only [Matrix.mul_assoc]

theorem commCompress_unitaryChannel {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Qᴴ = Q)
    {U : Matrix.unitaryGroup (Fin d) ℂ} (hU : (U : Matrix (Fin d) (Fin d) ℂ) * Q = Q * U) :
    CommCompress Q (unitaryChannel U) := fun σ => by
  rw [unitaryChannel_branch_apply, unitaryChannel_branch_apply]
  exact conj_compress hQ hU σ

theorem commCompress_chainG {Q : Matrix (Fin d) (Fin d) ℂ} {O : QComp d Unit}
    (hO : CommCompress Q O) :
    ∀ (q : ℕ) (U : Fin (q + 1) → QComp d Unit), (∀ i, CommCompress Q (U i)) →
      CommCompress Q (chainG O q U)
  | 0, _, hU => hU 0
  | q + 1, U, hU => fun σ => by
    simp only [chainG, qbind_unit_branch]
    rw [hU 0, hO, commCompress_chainG hO q (Fin.tail U) (fun i => hU i.succ)]

theorem commCompress_roundU {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Qᴴ = Q)
    (R : ClassicalRound d c a) (f : Fin c → Fin a) (hP : ∀ y, R.P y * Q = Q * R.P y)
    (hA : ∀ z, (R.ans z : Matrix (Fin d) (Fin d) ℂ) * Q = Q * R.ans z) :
    CommCompress Q (roundU R f) := fun σ => by
  rw [roundU_branch, roundU_branch, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => conj_compress hQ ?_ σ
  rw [Matrix.mul_assoc, hP, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]

theorem commCompress_mrChainG {q : ℕ} {Q : Matrix (Fin d) (Fin d) ℂ} {O : QComp d Unit}
    (hO : CommCompress Q O) (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
      (R : Fin k → ClassicalRound d c a), (∀ i, CommCompress Q (head i)) →
      (∀ j i, CommCompress Q (tail j i)) → (∀ j, CommCompress Q (roundU (R j) f)) →
      CommCompress Q (mrChainG O f k q₀ head tail R)
  | 0, q₀, head, _, _, hh, _, _ => commCompress_chainG hO q₀ head hh
  | k + 1, q₀, head, tail, R, hh, ht, hR => fun σ => by
    simp only [mrChainG, qbind_unit_branch]
    rw [commCompress_chainG hO q₀ head hh, hR 0,
      commCompress_mrChainG hO f k q (tail 0) (Fin.tail tail) (Fin.tail R) (ht 0)
        (fun j => ht j.succ) (fun j => hR j.succ)]

/-- A block diagonal operator commutes with every diagonal projector that factors through the
    labelling. -/
theorem BlockDiag.mul_diagB_comm {α : Type} {r : Fin d → α} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : BlockDiag r U) (g : α → Bool) :
    U * QROM.diagB (fun i => g (r i)) = QROM.diagB (fun i => g (r i)) * U := by
  ext i j
  simp only [QROM.diagB, mul_diagonal, diagonal_mul]
  by_cases h : r i = r j
  · grind
  · rw [hU i j h]
    simp

/-- A part of a round whose Kraus operators all lie in the range of `Q` is invariant under the
    compression by `Q`. -/
theorem roundPart_eq_compress {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Qᴴ = Q)
    (R : ClassicalRound d c a) (f : Fin c → Fin a) (D : Finset (Fin c))
    (hK : ∀ y ∈ D, Q * ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y) =
      (R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y)
    (σ : Matrix (Fin d) (Fin d) ℂ) : roundPart R f D σ = Q * roundPart R f D σ * Q := by
  unfold roundPart
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y hy => ?_
  conv_lhs => rw [← hK y hy]
  rw [conjTranspose_mul, hQ]
  simp only [Matrix.mul_assoc]

end Compress

/-! ## Diagonal projectors on a register with an ancilla -/

section KrDiag

variable {d c D : ℕ}

theorem kr_diagB (e : Fin (d * c) ≃ Fin D) (g₁ : Fin d → Bool) (g₂ : Fin c → Bool) :
    kr e (diagB g₁) (diagB g₂) = diagB fun i =>
      g₁ ((finProdEquiv d c).symm (e.symm i)).1 && g₂ ((finProdEquiv d c).symm (e.symm i)).2 := by
  ext i j
  obtain ⟨⟨x, z⟩, rfl⟩ := ((finProdEquiv d c).trans e).surjective i
  obtain ⟨⟨x', z'⟩, rfl⟩ := ((finProdEquiv d c).trans e).surjective j
  simp only [Equiv.trans_apply, kr_apply_pair, diagB, diagonal_apply, Equiv.symm_apply_apply,
    EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hx : x = x' <;> by_cases hz : z = z' <;> grind

theorem diagB_true : diagB (fun _ : Fin d => true) = 1 := by
  simp [diagB]

theorem diagB_mul_ancProj {g : Fin c → Bool} {y : Fin c} (hy : g y = true) :
    diagB g * ancProj y = ancProj y := by
  unfold diagB ancProj
  rw [diagonal_mul_diagonal]
  congr 1
  funext z
  by_cases hz : z = y
  · subst hz; simp [hy]
  · simp [hz]

end KrDiag

/-! ## The recorded run avoids the outcomes its final test excludes -/

section Avoid

variable {m n q c a : ℕ} [NeZero c]

omit [NeZero c] in
/-- The Kraus operators of a round lie in the range of `diagB p` after lifting along `k` more
    ancillas, when they do before. -/
theorem diagB_liftKLab_mul_liftKR : ∀ (k : ℕ) {W : ℕ} (R : ClassicalRound (m * n * W) c a)
    (p : Fin (m * n * W) → Bool) (z : Fin a) (y : Fin c),
    diagB p * ((R.ans z : Matrix _ _ ℂ) * R.P y) = (R.ans z : Matrix _ _ ℂ) * R.P y →
    diagB (liftKLab c k p) * (((liftKR c k R).ans z : Matrix _ _ ℂ) * (liftKR c k R).P y) =
      ((liftKR c k R).ans z : Matrix _ _ ℂ) * (liftKR c k R).P y
  | 0, _, _, _, _, _, h => h
  | k + 1, W, R, p, z, y, h => by
    refine diagB_liftKLab_mul_liftKR k (liftR (ancE m n W c) R) _ z y ?_
    have h1 : diagB (fun i => p (ancSplit m n W c i).1) =
        kr (ancE m n W c) (diagB p) (diagB fun _ => true) := by
      rw [kr_diagB]
      simp [ancSplit]
    change diagB (fun i => p (ancSplit m n W c i).1) *
      (kr (ancE m n W c) (R.ans z : Matrix _ _ ℂ) 1 * kr (ancE m n W c) (R.P y) 1) =
        kr (ancE m n W c) (R.ans z : Matrix _ _ ℂ) 1 * kr (ancE m n W c) (R.P y) 1
    grind [diagB_true, kr_mul, Matrix.one_mul, Matrix.mul_assoc]

/-- The Kraus operator of outcome `y ∈ Y` of the recorded round lies in the range of the
    projector onto the basis states whose ancilla digit lies in `Y`. -/
theorem diagB_mul_recordRound {d D : ℕ} (e : Fin (d * c) ≃ Fin D) (R : ClassicalRound d c a)
    (Y : Finset (Fin c)) (z : Fin a) {y : Fin c} (hy : y ∈ Y) :
    diagB (fun i => decide (((finProdEquiv d c).symm (e.symm i)).2 ∈ Y)) *
        (((recordRound e R).ans z : Matrix _ _ ℂ) * (recordRound e R).P y) =
      ((recordRound e R).ans z : Matrix _ _ ℂ) * (recordRound e R).P y := by
  have hK : ((recordRound e R).ans z : Matrix (Fin D) (Fin D) ℂ) * (recordRound e R).P y =
      kr e (R.ans z : Matrix (Fin d) (Fin d) ℂ) (ancProj y) * roundW e R := by
    rw [recordRound_ans_val]
    change kr e (R.ans z : Matrix (Fin d) (Fin d) ℂ) 1 * roundW e R *
      ((roundW e R)ᴴ * kr e 1 (ancProj y) * roundW e R) = _
    calc _ = kr e (R.ans z : Matrix (Fin d) (Fin d) ℂ) 1 * (roundW e R * (roundW e R)ᴴ) *
          kr e 1 (ancProj y) * roundW e R := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [roundW_mul_conjTranspose_self, Matrix.mul_one, kr_mul, Matrix.mul_one,
          Matrix.one_mul]
  have hQ : diagB (fun i => decide (((finProdEquiv d c).symm (e.symm i)).2 ∈ Y)) =
      kr e (diagB fun _ => true) (diagB fun y => decide (y ∈ Y)) := by
    rw [kr_diagB]
    simp
  rw [hK, hQ, diagB_true, ← Matrix.mul_assoc, kr_mul, Matrix.one_mul,
    diagB_mul_ancProj (by simpa using hy)]

variable [NeZero n]

/-- The recorded run with a final test that holds only at basis states whose recorded round
    outcomes all lie outside `Y` takes the same value on the full chain and on its branches
    whose round outcomes all lie outside `Y`. -/
theorem trace_diagB_recordFrom_eq_mrPartG (H : Fin m → Fin n) (f : Fin c → Fin a)
    (Y : Finset (Fin c)) :
    ∀ (k : ℕ) {W q₀ : ℕ} (X : MRH m n W q q₀ k c a) (G : Fin (m * n * ancW c k W) → Bool),
      (∀ i, G i = true → ∀ j, roundOutcomes m n c i j ∉ Y) →
      ∀ σ : Matrix (Fin (m * n * ancW c k W)) (Fin (m * n * ancW c k W)) ℂ,
        (diagB G * (mrChainG (oracleQ m n (ancW c k W) H) f k q₀
          (unitaryChannel ∘ (recordFrom k 0 X).head)
          (fun j => unitaryChannel ∘ (recordFrom k 0 X).tail j)
          (recordFrom k 0 X).rounds).branch () σ).trace =
        (diagB G * mrPartG (oracleQ m n (ancW c k W) H) f Y k q₀
          (unitaryChannel ∘ (recordFrom k 0 X).head)
          (fun j => unitaryChannel ∘ (recordFrom k 0 X).tail j)
          (recordFrom k 0 X).rounds σ).trace
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, W, q₀, X, G, hG, σ => by
    set X' := restH (recAt 0 X) with hX'
    set O := oracleQ m n (ancW c (k + 1) W) H with hO
    have hZ : restH (recordFrom (k + 1) 0 X) = recordFrom k 0 X' :=
      restH_recordFrom k 0 (recAt 0 X)
    have hZr : (recordFrom (k + 1) 0 X).rounds 0 =
        liftKR c k (recordRound (ancE m n W c) (X.rounds 0)) := by
      change (recordFrom k (0 + 1) (recAt 0 X)).rounds 0 = _
      rw [rounds_zero_recordFrom k 0]
      simp [recAt]
    set rest := mrChainG O f k q (unitaryChannel ∘ (recordFrom k 0 X').head)
      (fun j => unitaryChannel ∘ (recordFrom k 0 X').tail j) (recordFrom k 0 X').rounds
      with hrest
    set σ₁ := (chainG O q₀ (unitaryChannel ∘ (recordFrom (k + 1) 0 X).head)).branch () σ
      with hσ₁
    set R₀ := (recordFrom (k + 1) 0 X).rounds 0 with hR₀
    have hchain : (mrChainG O f (k + 1) q₀ (unitaryChannel ∘ (recordFrom (k + 1) 0 X).head)
        (fun j => unitaryChannel ∘ (recordFrom (k + 1) 0 X).tail j)
        (recordFrom (k + 1) 0 X).rounds).branch () σ =
        rest.branch () ((roundU R₀ f).branch () σ₁) := by
      simp only [mrChainG, qbind_unit_branch, hrest, ← hZ]
      rfl
    have hpart : mrPartG O f Y (k + 1) q₀ (unitaryChannel ∘ (recordFrom (k + 1) 0 X).head)
        (fun j => unitaryChannel ∘ (recordFrom (k + 1) 0 X).tail j)
        (recordFrom (k + 1) 0 X).rounds σ =
        mrPartG O f Y k q (unitaryChannel ∘ (recordFrom k 0 X').head)
          (fun j => unitaryChannel ∘ (recordFrom k 0 X').tail j) (recordFrom k 0 X').rounds
          (roundPart R₀ f Yᶜ σ₁) := by
      simp only [mrPartG, ← hZ]
      rfl
    -- the induction hypothesis on the branches whose outcome of round `0` lies outside `Y`
    have hG' : ∀ i, G i = true → ∀ j, roundOutcomes m n c (k := k) (w := W * c) i j ∉ Y := by
      intro i h j
      have := hG i h j.succ
      rwa [roundOutcomes_succ, Fin.cons_succ] at this
    have ih := trace_diagB_recordFrom_eq_mrPartG H f Y k X' G hG' (roundPart R₀ f Yᶜ σ₁)
    -- the branches whose outcome of round `0` lies in `Y`
    set ℓ : Fin (m * n * ancW c (k + 1) W) → Fin c :=
      liftKLab c k fun i => (ancSplit m n W c i).2 with hℓ
    set Q : Matrix (Fin (m * n * ancW c (k + 1) W)) (Fin (m * n * ancW c (k + 1) W)) ℂ :=
      diagB fun i => decide (ℓ i ∈ Y) with hQdef
    have hQ : Qᴴ = Q := diagB_conjTranspose _
    have hQl : Q = diagB (liftKLab c k fun i => decide ((ancSplit m n W c i).2 ∈ Y)) := by
      rw [hQdef]
      congr 1
      funext i
      grind [liftKLab_apply]
    have hτ : roundPart R₀ f Y σ₁ = Q * roundPart R₀ f Y σ₁ * Q := by
      refine roundPart_eq_compress hQ R₀ f Y (fun y hy => ?_) σ₁
      change Q * ((R₀.ans (f y) : Matrix _ _ ℂ) * R₀.P y) = (R₀.ans (f y) : Matrix _ _ ℂ) * R₀.P y
      rw [hZr, hQl]
      exact diagB_liftKLab_mul_liftKR k _ _ _ _
        (diagB_mul_recordRound (ancE m n W c) (X.rounds 0) Y (f y) hy)
    have hC : CommCompress Q rest := by
      obtain ⟨hBD, hOBD⟩ := restH_recAt_zero_BD X H ∅
      obtain ⟨⟨hh, ht, hP, hA⟩, ho⟩ := MRH.BD.recordFrom (H := H) (S := ∅) k 0 X' _ hBD hOBD
      have hcomm : ∀ {U : Matrix _ _ ℂ}, BlockDiag ℓ U → U * Q = Q * U := fun hU =>
        hU.mul_diagB_comm fun y => decide (y ∈ Y)
      exact commCompress_mrChainG (commCompress_unitaryChannel hQ (hcomm ho.1)) f k q _ _ _
        (fun i => commCompress_unitaryChannel hQ (hcomm (hh i)))
        (fun j i => commCompress_unitaryChannel hQ (hcomm (ht j i)))
        (fun j => commCompress_roundU hQ _ f (fun y => hcomm (hP j y)) (fun z => hcomm (hA j z)))
    have hGQ : diagB G * Q = 0 := by
      rw [hQdef, diagB_mul_diagB]
      have h0 : (fun i => G i && decide (ℓ i ∈ Y)) = fun _ => false := by
        funext i
        cases hGi : G i
        · rfl
        · have h := hG i hGi 0
          rw [roundOutcomes_succ, Fin.cons_zero] at h
          have hl : ℓ i = (ancSplit m n W c (ancDigits m n c k (w := W * c) i).1).2 := by
            exact liftKLab_apply c k _ i
          simp [hl, h]
      rw [h0]
      ext i j
      simp [diagB]
    have hbad : (diagB G * rest.branch () (roundPart R₀ f Y σ₁)).trace = 0 := by
      rw [hτ, hC, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGQ, Matrix.zero_mul, Matrix.zero_mul,
        trace_zero]
    rw [hchain, hpart, roundU_branch_eq_add R₀ f Y σ₁, map_add, Matrix.mul_add, trace_add, hbad,
      add_zero]
    exact ih

end Avoid

section AvoidAdv

variable {m n w q k c a : ℕ} [NeZero c] [NeZero n]

/-- A final test of the recorded adversary that holds only at basis states whose recorded round
    outcomes all lie outside `Y` has acceptance probability `prOutAvoidMRGen`: the run accepts
    and no round outcome lies in `Y`. -/
theorem prOutMRGen_recordGen_eq_prOutAvoidMRGen (A : QAdvMR m n w q k c a)
    (G : Fin (m * n * ancW c k w) → Bool) (Y : Finset (Fin c))
    (hG : ∀ i, G i = true → ∀ j, roundOutcomes m n c i j ∉ Y) (H : Fin m → Fin n)
    (f : Fin c → Fin a) :
    prOutMRGen (recordGen A G) H f = prOutAvoidMRGen (recordGen A G) H f Y := by
  rw [prOutMRGen_eq_ofReal, prOutAvoidMRGen]
  have hfin : (recordGen A G).final = diagB G := rfl
  have hseg : (fun i => ((recordGen A G).seg 0 i).toQComp) =
      unitaryChannel ∘ (recordFrom k 0 A.toMRH).head := by
    funext i
    simp [recordGen, recordMR, QAdvMR.toGen]
  have htail : (fun j i => (Fin.tail (recordGen A G).seg j i).toQComp) =
      fun j => unitaryChannel ∘ (recordFrom k 0 A.toMRH).tail j := by
    funext j i
    simp [recordGen, recordMR, QAdvMR.toGen, Fin.tail]
  simp only [QAdvMRGen.measure, measProj_branch_true, hfin, diagB_conjTranspose,
    trace_proj_mul_mul_proj (diagB_mul_self G), hseg, htail]
  exact congrArg (fun t : ℂ => ENNReal.ofReal t.re)
    (trace_diagB_recordFrom_eq_mrPartG H f Y k A.toMRH G hG _)

end AvoidAdv

end CatCrypt.Quantum.QROM
