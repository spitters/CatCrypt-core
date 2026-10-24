/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.FiatShamir
public import CatCryptCore.ForMathlib.Matrix.ProjectorRewinding

/-!
# The binary rewinding extractor for the interactive Fiat–Shamir game

Unruh's rewinding extractor (EUROCRYPT 2012, "Quantum Proofs of Knowledge") for
the interactive game `fsInteractive A V H` of `FiatShamir`: a uniform slot `t`,
the run of `A` against `H` up to the slot, the measurement of the commitment
`x`, a uniform challenge `θ₁`, the response unitary `fsSufU A H t x θ₁`, the
two-outcome measurement of `V(x, θ₁)`, the inverse of the response unitary, a
uniform challenge `θ₂`, the response unitary `fsSufU A H t x θ₂` and the
two-outcome measurement of `V(x, θ₂)`.

With `P_θ = U_θ⁻¹ · V(x, θ) · U_θ` for the response unitary `U_θ` and the state
`σ` after the commitment measurement, the acceptance probability of the
interactive game is the sum over the slot and the commitment of
`n⁻¹ Σ_θ tr (P_θ σ)`, and the extractor's event (both accept, `θ₁ ≠ θ₂`) has the
sum of `n⁻² Σ_{θ₁ ≠ θ₂} tr (P_θ₂ P_θ₁ σ P_θ₁ P_θ₂)`. The density form of the
rewinding inequality, `Matrix.rewinding_density_trace`, and Hölder's inequality
over the slots and the commitments give the bound `p · (p² − 1/n)`.

The verifier projectors are required to commute with the projectors of the
commitment measurement, since the interactive game measures the commitment
register before the verifier.

## Main definitions

* `conjProj U V` — the projector `U⁻¹ · V · U`
* `rewindExtractWith M A H` — the rewinding extractor with the measurements
  `M x θ` in place of the verifier measurement
* `rewindExtract A V H` — the binary rewinding extractor
* `rewindAccept` — both measurements accept and the challenges are distinct

## Main results

* `rewindExtract_bound` — `p · (p² − 1/n) ≤ Pr[rewindAccept]` for the
  acceptance probability `p` of `fsInteractive A V H`
* `rewindExtractWith_eq` — an extractor whose measurements coarsen to the
  verifier measurements has the event probability of `rewindExtract`

## References

* [Unruh — Quantum Proofs of Knowledge, EUROCRYPT 2012], Lemma 7
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
  CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Conjugated projectors and traces -/

section Conj

variable {d : ℕ}

/-- The projector `U⁻¹ · V · U` for a unitary `U`. -/
def conjProj (U : Matrix.unitaryGroup (Fin d) ℂ) (V : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * V * U

theorem isStarProjection_conjProj (U : Matrix.unitaryGroup (Fin d) ℂ)
    {V : Matrix (Fin d) (Fin d) ℂ} (hH : Vᴴ = V) (hI : V * V = V) :
    IsStarProjection (conjProj U V) := by
  have hU : (U : Matrix (Fin d) (Fin d) ℂ) * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp U.2
    simpa only [star_eq_conjTranspose] using this
  refine ⟨?_, ?_⟩
  · show conjProj U V * conjProj U V = conjProj U V
    simp only [conjProj, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix (Fin d) (Fin d) ℂ) _ (V * _), hU, Matrix.one_mul,
      ← Matrix.mul_assoc V V, hI]
  · show (conjProj U V)ᴴ = conjProj U V
    simp only [conjProj, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc]

/-- For a Hermitian idempotent `V`, `tr (V X Vᴴ) = tr (V X)`. -/
theorem trace_proj_mul_mul_conjTranspose {V : Matrix (Fin d) (Fin d) ℂ} (hH : Vᴴ = V)
    (hI : V * V = V) (X : Matrix (Fin d) (Fin d) ℂ) : (V * X * Vᴴ).trace = (V * X).trace := by
  rw [trace_mul_cycle, hH, hI]

/-- `tr (V (U Y Uᴴ) Vᴴ) = tr (U⁻¹ V U · Y)`. -/
theorem trace_meas_conj (U : Matrix.unitaryGroup (Fin d) ℂ) {V : Matrix (Fin d) (Fin d) ℂ}
    (hH : Vᴴ = V) (hI : V * V = V) (Y : Matrix (Fin d) (Fin d) ℂ) :
    (V * ((U : Matrix (Fin d) (Fin d) ℂ) * Y * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) * Vᴴ).trace =
      (conjProj U V * Y).trace := by
  rw [trace_proj_mul_mul_conjTranspose hH hI, ← Matrix.mul_assoc, trace_mul_cycle, conjProj]
  simp only [Matrix.mul_assoc]

/-- Rewinding by `U⁻¹` after the measurement of `V` in the frame of `U` is the
    conjugation by `U⁻¹ V U`. -/
theorem inv_conj_meas_conj (U : Matrix.unitaryGroup (Fin d) ℂ) {V : Matrix (Fin d) (Fin d) ℂ}
    (hH : Vᴴ = V) (σ : Matrix (Fin d) (Fin d) ℂ) :
    ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) *
        (V * ((U : Matrix (Fin d) (Fin d) ℂ) * σ * (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) * Vᴴ) *
        ((U⁻¹ : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)ᴴ =
      conjProj U V * σ * conjProj U V := by
  simp only [UnitaryGroup.inv_val, star_eq_conjTranspose, conjTranspose_conjTranspose, hH,
    conjProj, Matrix.mul_assoc]

/-- `tr (P X)` is nonnegative for an orthogonal projector `P` and a positive
    semidefinite `X`. -/
theorem trace_re_starProj_mul_nonneg {P : Matrix (Fin d) (Fin d) ℂ} (hP : IsStarProjection P)
    {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.PosSemidef) : 0 ≤ (P * X).trace.re := by
  have hs : Pᴴ = P := hP.isSelfAdjoint
  have h := trace_proj_mul_mul_conjTranspose hs hP.isIdempotentElem.eq X
  rw [← h]
  exact trace_re_nonneg_of_psd (hX.mul_mul_conjTranspose_same P)

/-- `tr (P₂ P₁ X P₁ P₂)` is nonnegative for orthogonal projectors and a positive
    semidefinite `X`. -/
theorem trace_re_starProj_sandwich_nonneg {P₁ P₂ : Matrix (Fin d) (Fin d) ℂ}
    (hP₁ : IsStarProjection P₁) (hP₂ : IsStarProjection P₂) {X : Matrix (Fin d) (Fin d) ℂ}
    (hX : X.PosSemidef) : 0 ≤ (P₂ * P₁ * X * P₁ * P₂).trace.re := by
  have h1 : P₁ᴴ = P₁ := hP₁.isSelfAdjoint
  have h2 : P₂ᴴ = P₂ := hP₂.isSelfAdjoint
  have := hX.mul_mul_conjTranspose_same (P₂ * P₁)
  rw [conjTranspose_mul, h1, h2, ← Matrix.mul_assoc] at this
  exact trace_re_nonneg_of_psd this

/-- `tr (P₂ P₁ X P₁ P₂) = tr (P₂ (P₁ X P₁))` for an idempotent `P₂`. -/
theorem trace_sandwich_eq {P₁ P₂ : Matrix (Fin d) (Fin d) ℂ} (hI : P₂ * P₂ = P₂)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    (P₂ * P₁ * X * P₁ * P₂).trace = (P₂ * (P₁ * X * P₁)).trace := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hI]
  simp only [Matrix.mul_assoc]

/-- The real traces of the branches of an instrument sum to at most the trace of
    its positive semidefinite input. -/
theorem sum_trace_re_branch_le {α : Type} [Fintype α] (I : QComp d α)
    {σ : Matrix (Fin d) (Fin d) ℂ} (hσ : σ.PosSemidef) :
    ∑ a, (I.branch a σ).trace.re ≤ σ.trace.re := by
  have h := I.branch_stp σ hσ
  rwa [tsum_fintype, Complex.re_sum] at h

end Conj

/-! ## One round of the extractor -/

section Round

variable {d n : ℕ} [NeZero n]

/-- One round of the extractor: a uniform challenge `θ`, the unitary `U θ`, the
    measurement of `V θ` and the continuation `k θ b`, whose rejecting
    continuations `k θ false` never accept. The accepting trace is the average
    over `θ` of the accepting trace of `k θ true` on `V θ (U θ Y U θᴴ) V θᴴ`. -/
theorem trace_re_round (U : Fin n → Matrix.unitaryGroup (Fin d) ℂ)
    (V : Fin n → Matrix (Fin d) (Fin d) ℂ) (hH : ∀ θ, (V θ)ᴴ = V θ)
    (hI : ∀ θ, V θ * V θ = V θ) (k : Fin n → Bool → QComp d Bool)
    (hk : ∀ θ Z, ((k θ false).branch true Z).trace.re = 0) (Y : Matrix (Fin d) (Fin d) ℂ) :
    ((QComp.qbind (uniformQ (Fin n)) fun θ =>
        QComp.qbind (unitaryChannel (U θ)) fun _ =>
          QComp.qbind (measProj (V θ) (hH θ) (hI θ)) fun b => k θ b).branch true Y).trace.re =
      (n : ℝ)⁻¹ * ∑ θ, ((k θ true).branch true
        (V θ * ((U θ : Matrix (Fin d) (Fin d) ℂ) * Y * (U θ : Matrix (Fin d) (Fin d) ℂ)ᴴ) *
          (V θ)ᴴ)).trace.re := by
  rw [trace_re_qbind_branch, Finset.mul_sum]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [qbind_unit_branch, qbind_bool_branch, Matrix.trace_add, Complex.add_re, hk, zero_add,
    uniformQ_branch_apply, unitaryChannel_branch_apply, measProj_branch_true]
  simp only [Matrix.mul_smul, Matrix.smul_mul, map_smul, Matrix.trace_smul, smul_eq_mul,
    Complex.re_ofReal_mul, Fintype.card_fin]

end Round

/-! ## The commitment measurement before the verifier -/

section MeasXVer

variable {m n w : ℕ}

/-- `tr (V (U Y Uᴴ)) = tr (U⁻¹ V U · Y)`. -/
theorem trace_mul_conj (U : Matrix.unitaryGroup (Fin (m * n * w)) ℂ)
    (V Y : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (V * ((U : Matrix _ _ ℂ) * Y * (U : Matrix _ _ ℂ)ᴴ)).trace = (conjProj U V * Y).trace := by
  rw [← Matrix.mul_assoc, trace_mul_cycle, conjProj]
  simp only [Matrix.mul_assoc]

/-- A projector `V` commuting with the projectors of the commitment measurement:
    the measurement of the commitment followed by the measurement of `V` accepts
    with trace `tr (V Z)`. -/
theorem trace_measX_measProj {V : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ}
    (hH : Vᴴ = V) (hI : V * V = V) (hV : ∀ x', V * projS m n w {x'} = projS m n w {x'} * V)
    (Z : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    ((QComp.qbind (measX m n w) fun _ => measProj V hH hI).branch true Z).trace =
      (V * Z).trace := by
  rw [qbind_branch_apply, tsum_fintype, Matrix.trace_sum]
  have hx : ∀ x', ((measProj V hH hI).branch true ((measX m n w).branch x' Z)).trace =
      (V * (projS m n w {x'} * Z)).trace := by
    intro x'
    rw [measX_branch, measProj_branch_true, trace_proj_mul_mul_conjTranspose hH hI,
      projS_conjTranspose, ← Matrix.mul_assoc, trace_mul_cycle, ← hV, Matrix.mul_assoc,
      ← Matrix.mul_assoc (projS m n w {x'}) (projS m n w {x'}), projS_mul_self]
  simp only [hx, ← Matrix.trace_sum, ← Finset.mul_sum, ← Finset.sum_mul, sum_projS_singleton,
    Matrix.one_mul]

end MeasXVer

/-! ## The extractor -/

section Extractor

variable {m n w q : ℕ} [NeZero n]

/-- The two-outcome measurement of the verifier projector `V(x, θ)`. -/
def QVerifier.meas (V : QVerifier m n w) (x : Fin m) (θ : Fin n) : QComp (m * n * w) Bool :=
  measProj (V.proj x θ) (V.proj_conjTranspose x θ) (V.proj_mul_self x θ)

/-- The rewinding extractor with the measurements `M x θ`: a uniform slot `t`;
    the run of `A` against `H` up to the slot; the measurement of the commitment
    `x`; a uniform challenge `θ₁`; the response unitary `fsSufU A H t x θ₁`; the
    measurement `M x θ₁` with outcome `o₁`; the inverse of the response unitary;
    a uniform challenge `θ₂`; the response unitary `fsSufU A H t x θ₂`; the
    measurement `M x θ₂` with outcome `o₂`. The output is
    `(x, (θ₁, o₁), (θ₂, o₂))`. -/
def rewindExtractWith {β : Type} (M : Fin m → Fin n → QComp (m * n * w) β) (A : QAdv m n w q)
    (H : Fin m → Fin n) : QComp (m * n * w) (Fin m × (Fin n × β) × (Fin n × β)) :=
  QComp.qbind (uniformQ (Option (Fin q × Bool))) fun t =>
    QComp.qbind (preChain (oracleQ m n w H) (mrSlot t) q A.U) fun _ =>
      QComp.qbind (measX m n w) fun x =>
        QComp.qbind (uniformQ (Fin n)) fun θ₁ =>
          QComp.qbind (unitaryChannel (fsSufU A H t x θ₁)) fun _ =>
            QComp.qbind (M x θ₁) fun o₁ =>
              QComp.qbind (unitaryChannel (fsSufU A H t x θ₁)⁻¹) fun _ =>
                QComp.qbind (uniformQ (Fin n)) fun θ₂ =>
                  QComp.qbind (unitaryChannel (fsSufU A H t x θ₂)) fun _ =>
                    QComp.qbind (M x θ₂) fun o₂ =>
                      QComp.qpure (x, (θ₁, o₁), (θ₂, o₂))

/-- The binary rewinding extractor: `rewindExtractWith` with the two-outcome
    measurements of the verifier projectors `V(x, θ)`. -/
def rewindExtract (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n) :
    QComp (m * n * w) (Fin m × (Fin n × Bool) × (Fin n × Bool)) :=
  rewindExtractWith V.meas A H

/-- Both measurements of the binary extractor accept and the challenges are
    distinct. -/
def rewindAccept : Fin m × (Fin n × Bool) × (Fin n × Bool) → Bool
  | (_, (θ₁, b₁), (θ₂, b₂)) => b₁ && b₂ && decide (θ₁ ≠ θ₂)

/-- An extractor whose measurements `M x θ`, relabelled by `g x θ`, are the
    verifier measurements has, for an event `e` that reads its outcomes through
    `g`, the event probability of the binary extractor. -/
theorem rewindExtractWith_eq {β : Type} (M : Fin m → Fin n → QComp (m * n * w) β)
    (V : QVerifier m n w) (g : Fin m → Fin n → β → Bool)
    (hM : ∀ x θ, QComp.qbind (M x θ) (fun o => QComp.qpure (g x θ o)) = V.meas x θ)
    (e : Fin m × (Fin n × β) × (Fin n × β) → Bool)
    (he : ∀ x θ₁ o₁ θ₂ o₂,
      e (x, (θ₁, o₁), (θ₂, o₂)) = (g x θ₁ o₁ && g x θ₂ o₂ && decide (θ₁ ≠ θ₂)))
    (A : QAdv m n w q) (H : Fin m → Fin n) :
    QComp.qbind (rewindExtractWith M A H) (fun o => QComp.qpure (e o)) =
      QComp.qbind (rewindExtract A V H) (fun o => QComp.qpure (rewindAccept o)) := by
  simp only [rewindExtract, rewindExtractWith, ← hM, QComp.qbind_assoc, QComp.qpure_qbind, he,
    rewindAccept]

/-- The state after the slot `t`, the run up to the slot and the outcome `x` of
    the commitment measurement, weighted by the probability of the slot. -/
def rewindState (A : QAdv m n w q) (H : Fin m → Fin n) (t : Option (Fin q × Bool)) (x : Fin m) :
    Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ :=
  (measX m n w).branch x ((preChain (oracleQ m n w H) (mrSlot t) q A.U).branch ()
    ((uniformQ (Option (Fin q × Bool))).branch t A.init.val))

theorem rewindState_psd (A : QAdv m n w q) (H : Fin m → Fin n) (t : Option (Fin q × Bool))
    (x : Fin m) : (rewindState A H t x).PosSemidef :=
  QComp.branch_psd _ _ _ (QComp.branch_psd _ _ _ (QComp.branch_psd _ _ _ A.init.psd))

/-- The states `rewindState A H t x` have total trace at most one. -/
theorem sum_trace_re_rewindState_le (A : QAdv m n w q) (H : Fin m → Fin n) :
    ∑ t, ∑ x, (rewindState A H t x).trace.re ≤ 1 := by
  set ρ := A.init.val
  calc ∑ t, ∑ x, (rewindState A H t x).trace.re
      ≤ ∑ t, ((preChain (oracleQ m n w H) (mrSlot t) q A.U).branch ()
          ((uniformQ (Option (Fin q × Bool))).branch t ρ)).trace.re :=
        Finset.sum_le_sum fun t _ => sum_trace_re_branch_le _
          (QComp.branch_psd _ _ _ (QComp.branch_psd _ _ _ A.init.psd))
    _ ≤ ∑ t, ((uniformQ (Option (Fin q × Bool))).branch t ρ).trace.re :=
        Finset.sum_le_sum fun t _ => by
          simpa using sum_trace_re_branch_le (preChain (oracleQ m n w H) (mrSlot t) q A.U)
            (QComp.branch_psd _ t _ A.init.psd)
    _ ≤ ρ.trace.re := sum_trace_re_branch_le _ A.init.psd
    _ = 1 := by rw [A.init.tr_one, Complex.one_re]

/-- The accepting trace of a program that draws the slot, runs up to it and
    measures the commitment, then runs `K t x`. -/
theorem trace_re_outer (A : QAdv m n w q) (H : Fin m → Fin n)
    (K : Option (Fin q × Bool) → Fin m → QComp (m * n * w) Bool) :
    ((QComp.qbind (uniformQ (Option (Fin q × Bool))) fun t =>
        QComp.qbind (preChain (oracleQ m n w H) (mrSlot t) q A.U) fun _ =>
          QComp.qbind (measX m n w) fun x => K t x).branch true A.init.val).trace.re =
      ∑ t, ∑ x, ((K t x).branch true (rewindState A H t x)).trace.re := by
  rw [trace_re_qbind_branch]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [qbind_unit_branch, trace_re_qbind_branch]
  rfl

/-- The projector `P_θ = U_θ⁻¹ V(x, θ) U_θ` of the response unitary on the slot
    `t` and the commitment `x`. -/
def rewindProj (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n)
    (t : Option (Fin q × Bool)) (x : Fin m) (θ : Fin n) :
    Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ :=
  conjProj (fsSufU A H t x θ) (V.proj x θ)

theorem isStarProjection_rewindProj (A : QAdv m n w q) (V : QVerifier m n w)
    (H : Fin m → Fin n) (t : Option (Fin q × Bool)) (x : Fin m) (θ : Fin n) :
    IsStarProjection (rewindProj A V H t x θ) :=
  isStarProjection_conjProj _ (V.proj_conjTranspose x θ) (V.proj_mul_self x θ)

/-- The accepting trace of the interactive game is the sum over the slot and the
    commitment of `n⁻¹ Σ_θ tr (P_θ σ)`. -/
theorem trace_re_fsInteractive (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n)
    (hV : ∀ x θ x', V.proj x θ * projS m n w {x'} = projS m n w {x'} * V.proj x θ) :
    ((fsInteractive A V H).branch true A.init.val).trace.re =
      ∑ t, ∑ x, (n : ℝ)⁻¹ * ∑ θ, (rewindProj A V H t x θ * rewindState A H t x).trace.re := by
  rw [fsInteractive_eq_split, trace_re_outer]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun x _ => ?_
  rw [trace_re_qbind_branch, Finset.mul_sum]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [qbind_unit_branch, uniformQ_branch_apply, unitaryChannel_branch_apply]
  erw [trace_measX_measProj (V.proj_conjTranspose x θ) (V.proj_mul_self x θ) (hV x θ)]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Complex.re_ofReal_mul, Fintype.card_fin, trace_mul_conj, rewindProj]

/-- The accepting trace of the binary extractor's event is the sum over the slot
    and the commitment of `n⁻² Σ_{θ₁ ≠ θ₂} tr (P_θ₂ (P_θ₁ σ P_θ₁))`. -/
theorem trace_re_rewindExtract (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n) :
    ((QComp.qbind (rewindExtract A V H) fun o => QComp.qpure (rewindAccept o)).branch true
        A.init.val).trace.re =
      ∑ t, ∑ x, (n : ℝ)⁻¹ * ∑ θ₁, (n : ℝ)⁻¹ * ∑ θ₂, if θ₁ = θ₂ then 0 else
        (rewindProj A V H t x θ₂ * (rewindProj A V H t x θ₁ * rewindState A H t x *
          rewindProj A V H t x θ₁)).trace.re := by
  have hform : QComp.qbind (rewindExtract A V H) (fun o => QComp.qpure (rewindAccept o)) =
      QComp.qbind (uniformQ (Option (Fin q × Bool))) fun t =>
        QComp.qbind (preChain (oracleQ m n w H) (mrSlot t) q A.U) fun _ =>
          QComp.qbind (measX m n w) fun x =>
            QComp.qbind (uniformQ (Fin n)) fun θ₁ =>
              QComp.qbind (unitaryChannel (fsSufU A H t x θ₁)) fun _ =>
                QComp.qbind (measProj (V.proj x θ₁) (V.proj_conjTranspose x θ₁)
                    (V.proj_mul_self x θ₁)) fun b₁ =>
                  QComp.qbind (unitaryChannel (fsSufU A H t x θ₁)⁻¹) fun _ =>
                    QComp.qbind (uniformQ (Fin n)) fun θ₂ =>
                      QComp.qbind (unitaryChannel (fsSufU A H t x θ₂)) fun _ =>
                        QComp.qbind (measProj (V.proj x θ₂) (V.proj_conjTranspose x θ₂)
                            (V.proj_mul_self x θ₂)) fun b₂ =>
                          QComp.qpure (b₁ && b₂ && decide (θ₁ ≠ θ₂)) := by
    simp only [rewindExtract, rewindExtractWith, QVerifier.meas, QComp.qbind_assoc,
      QComp.qpure_qbind, rewindAccept]
  rw [hform, trace_re_outer]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun x _ => ?_
  have h2 : ∀ (b₁ : Bool) (θ₁ : Fin n) (Y : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ),
      ((QComp.qbind (uniformQ (Fin n)) fun θ₂ =>
        QComp.qbind (unitaryChannel (fsSufU A H t x θ₂)) fun _ =>
          QComp.qbind (measProj (V.proj x θ₂) (V.proj_conjTranspose x θ₂)
              (V.proj_mul_self x θ₂)) fun b₂ =>
            QComp.qpure (b₁ && b₂ && decide (θ₁ ≠ θ₂))).branch true Y).trace.re =
        (n : ℝ)⁻¹ * ∑ θ₂, if b₁ && decide (θ₁ ≠ θ₂) then
          (rewindProj A V H t x θ₂ * Y).trace.re else 0 := by
    intro b₁ θ₁ Y
    rw [trace_re_round (fun θ₂ => fsSufU A H t x θ₂) (V.proj x) (V.proj_conjTranspose x)
      (V.proj_mul_self x) (fun θ₂ b₂ => QComp.qpure (b₁ && b₂ && decide (θ₁ ≠ θ₂)))
      (fun θ₂ Z => by simp [qpure_branch_apply])]
    refine congrArg _ (Finset.sum_congr rfl fun θ₂ _ => ?_)
    simp only [qpure_branch_apply, Bool.and_true, @eq_comm Bool true]
    split_ifs
    · rw [trace_meas_conj _ (V.proj_conjTranspose x θ₂) (V.proj_mul_self x θ₂), rewindProj]
    · simp
  rw [trace_re_round (fun θ₁ => fsSufU A H t x θ₁) (V.proj x) (V.proj_conjTranspose x)
    (V.proj_mul_self x) _ (fun θ₁ Z => by
      rw [qbind_unit_branch, h2]; simp)]
  refine congrArg _ (Finset.sum_congr rfl fun θ₁ _ => ?_)
  rw [qbind_unit_branch, h2, unitaryChannel_branch_apply,
    inv_conj_meas_conj _ (V.proj_conjTranspose x θ₁)]
  refine congrArg _ (Finset.sum_congr rfl fun θ₂ _ => ?_)
  by_cases h : θ₁ = θ₂ <;> simp [h, rewindProj]

omit [NeZero n] in
/-- The extractor's event at one slot and commitment: the double average over
    the challenges minus its diagonal `θ₁ = θ₂`. -/
theorem rewind_offDiag_eq {d : ℕ} (P : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ θ, IsStarProjection (P θ)) (σ : Matrix (Fin d) (Fin d) ℂ) :
    (n : ℝ)⁻¹ * ∑ θ₁, (n : ℝ)⁻¹ * ∑ θ₂, (if θ₁ = θ₂ then 0 else
        (P θ₂ * (P θ₁ * σ * P θ₁)).trace.re) =
      ((n : ℝ) ^ 2)⁻¹ * ∑ θ₁, ∑ θ₂, (P θ₂ * P θ₁ * σ * P θ₁ * P θ₂).trace.re -
        (n : ℝ)⁻¹ * ((n : ℝ)⁻¹ * ∑ θ, (P θ * σ).trace.re) := by
  have hs : ∀ θ₁ θ₂, (P θ₂ * P θ₁ * σ * P θ₁ * P θ₂).trace.re =
      (P θ₂ * (P θ₁ * σ * P θ₁)).trace.re := fun θ₁ θ₂ => by
    rw [trace_sandwich_eq (hP θ₂).isIdempotentElem.eq]
  have hd : ∀ θ, (P θ * (P θ * σ * P θ)).trace.re = (P θ * σ).trace.re := fun θ => by
    have hI := (hP θ).isIdempotentElem.eq
    simp only [← Matrix.mul_assoc, hI]
    rw [trace_mul_comm]
    simp only [← Matrix.mul_assoc, hI]
  have hite : ∀ θ₁, ∑ θ₂, (if θ₁ = θ₂ then 0 else (P θ₂ * (P θ₁ * σ * P θ₁)).trace.re) =
      ∑ θ₂, (P θ₂ * (P θ₁ * σ * P θ₁)).trace.re - (P θ₁ * σ).trace.re := fun θ₁ => by
    rw [← hd θ₁, eq_sub_iff_add_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ θ₁),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ θ₁), ite_eq_left rfl, zero_add, add_comm]
    refine congrArg _ (Finset.sum_congr rfl fun θ₂ h => ?_)
    rw [ite_eq_right (Finset.ne_of_mem_erase h).symm]
  simp only [hite, hs, ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

omit [NeZero n] in
/-- From `p ³ ≤ F` with `0 ≤ p`: `p · (p² − 1/n) ≤ F − p/n` in `ℝ≥0∞`. -/
theorem ofReal_mul_sub_inv_le (n : ℕ) [NeZero n] {p F : ℝ} (hp0 : 0 ≤ p) (h : p ^ 3 ≤ F) :
    ENNReal.ofReal p * (ENNReal.ofReal p ^ 2 - (n : ℝ≥0∞)⁻¹) ≤
      ENNReal.ofReal (F - (n : ℝ)⁻¹ * p) := by
  have hn : (n : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((n : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr (NeZero.pos n)), ENNReal.ofReal_natCast]
  rw [hn, ← ENNReal.ofReal_pow hp0, ← ENNReal.ofReal_sub _ (inv_nonneg.mpr n.cast_nonneg),
    ← ENNReal.ofReal_mul hp0]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : p * (p ^ 2 - (n : ℝ)⁻¹) = p ^ 3 - (n : ℝ)⁻¹ * p := by ring
  rw [e]
  linarith

/-- **The rewinding bound for the binary extractor** (Unruh 2012, Lemma 7). For
    a verifier whose projectors commute with the projectors of the commitment
    measurement and the acceptance probability `p` of the interactive game
    `fsInteractive A V H`, the extractor `rewindExtract A V H` outputs two
    accepting outcomes with distinct challenges with probability at least
    `p · (p² − 1/n)`. -/
theorem rewindExtract_bound (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n)
    (hV : ∀ x θ x', V.proj x θ * projS m n w {x'} = projS m n w {x'} * V.proj x θ) :
    prTrue_Q (fsInteractive A V H) A.init *
        (prTrue_Q (fsInteractive A V H) A.init ^ 2 - (n : ℝ≥0∞)⁻¹) ≤
      prTrue_Q (QComp.qbind (rewindExtract A V H) fun o => QComp.qpure (rewindAccept o))
        A.init := by
  unfold prTrue_Q
  rw [trace_re_fsInteractive A V H hV, trace_re_rewindExtract]
  have hP := isStarProjection_rewindProj A V H
  rw [Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun x _ =>
    rewind_offDiag_eq _ (hP t x) (rewindState A H t x)]
  set pR := ∑ t, ∑ x, (n : ℝ)⁻¹ * ∑ θ,
    (rewindProj A V H t x θ * rewindState A H t x).trace.re with hpR
  set FR := ∑ t, ∑ x, ((n : ℝ) ^ 2)⁻¹ * ∑ θ₁, ∑ θ₂, (rewindProj A V H t x θ₂ *
    rewindProj A V H t x θ₁ * rewindState A H t x * rewindProj A V H t x θ₁ *
      rewindProj A V H t x θ₂).trace.re with hFR
  set T := ∑ t, ∑ x, (rewindState A H t x).trace.re with hT
  have ha0 : ∀ t x, 0 ≤ (n : ℝ)⁻¹ * ∑ θ,
      (rewindProj A V H t x θ * rewindState A H t x).trace.re := fun t x =>
    mul_nonneg (inv_nonneg.mpr n.cast_nonneg) (Finset.sum_nonneg fun θ _ =>
      trace_re_starProj_mul_nonneg (hP t x θ) (rewindState_psd A H t x))
  have hF0 : ∀ t x, 0 ≤ ((n : ℝ) ^ 2)⁻¹ * ∑ θ₁, ∑ θ₂, (rewindProj A V H t x θ₂ *
      rewindProj A V H t x θ₁ * rewindState A H t x * rewindProj A V H t x θ₁ *
        rewindProj A V H t x θ₂).trace.re := fun t x =>
    mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (Finset.sum_nonneg fun θ₁ _ =>
      Finset.sum_nonneg fun θ₂ _ =>
      trace_re_starProj_sandwich_nonneg (hP t x θ₁) (hP t x θ₂) (rewindState_psd A H t x))
  have hT0 : ∀ t x, 0 ≤ (rewindState A H t x).trace.re := fun t x =>
    trace_re_nonneg_of_psd (rewindState_psd A H t x)
  have hp0 : 0 ≤ pR := Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun x _ => ha0 t x
  have hFR0 : 0 ≤ FR := Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun x _ => hF0 t x
  have hT1 : T ≤ 1 := sum_trace_re_rewindState_le A H
  have hTn : 0 ≤ T := Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun x _ => hT0 t x
  have hHolder : pR ^ 3 ≤ FR * T ^ 2 := by
    have h := Real.pow_three_sum_le_sum_mul_sq_sum
      (Finset.univ : Finset (Option (Fin q × Bool) × Fin m))
      (fun i => (n : ℝ)⁻¹ * ∑ θ,
        (rewindProj A V H i.1 i.2 θ * rewindState A H i.1 i.2).trace.re)
      (fun i => (rewindState A H i.1 i.2).trace.re)
      (fun i => ((n : ℝ) ^ 2)⁻¹ * ∑ θ₁, ∑ θ₂, (rewindProj A V H i.1 i.2 θ₂ *
        rewindProj A V H i.1 i.2 θ₁ * rewindState A H i.1 i.2 * rewindProj A V H i.1 i.2 θ₁ *
          rewindProj A V H i.1 i.2 θ₂).trace.re)
      (fun i _ => ha0 i.1 i.2) (fun i _ => hT0 i.1 i.2) (fun i _ => hF0 i.1 i.2)
      (fun i _ => Matrix.rewinding_density_trace (hP i.1 i.2) (rewindState_psd A H i.1 i.2))
    simp only [Fintype.sum_prod_type] at h
    exact h
  have hE : ∑ t, ∑ x, (((n : ℝ) ^ 2)⁻¹ * ∑ θ₁, ∑ θ₂, (rewindProj A V H t x θ₂ *
      rewindProj A V H t x θ₁ * rewindState A H t x * rewindProj A V H t x θ₁ *
        rewindProj A V H t x θ₂).trace.re - (n : ℝ)⁻¹ * ((n : ℝ)⁻¹ * ∑ θ,
          (rewindProj A V H t x θ * rewindState A H t x).trace.re)) =
      FR - (n : ℝ)⁻¹ * pR := by
    rw [hFR, hpR]
    simp only [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hE]
  exact ofReal_mul_sub_inv_le n hp0
    (hHolder.trans (mul_le_of_le_one_right hFR0 (pow_le_one₀ hTn hT1)))

/-- **The rewinding bound for an extractor with coarsening measurements.** If
    the measurements `M x θ`, relabelled by `g x θ`, are the two-outcome
    measurements of the verifier projectors, which commute with the projectors
    of the commitment measurement, and the event `e` reads the outcomes through
    `g`, then `rewindExtractWith M A H` satisfies `e` with probability at least
    `p · (p² − 1/n)` for the acceptance probability `p` of `fsInteractive A V H`. -/
theorem rewindExtractWith_bound {β : Type} (M : Fin m → Fin n → QComp (m * n * w) β)
    (V : QVerifier m n w) (g : Fin m → Fin n → β → Bool)
    (hM : ∀ x θ, QComp.qbind (M x θ) (fun o => QComp.qpure (g x θ o)) =
      measProj (V.proj x θ) (V.proj_conjTranspose x θ) (V.proj_mul_self x θ))
    (e : Fin m × (Fin n × β) × (Fin n × β) → Bool)
    (he : ∀ x θ₁ o₁ θ₂ o₂,
      e (x, (θ₁, o₁), (θ₂, o₂)) = (g x θ₁ o₁ && g x θ₂ o₂ && decide (θ₁ ≠ θ₂)))
    (hV : ∀ x θ x', V.proj x θ * projS m n w {x'} = projS m n w {x'} * V.proj x θ)
    (A : QAdv m n w q) (H : Fin m → Fin n) :
    prTrue_Q (fsInteractive A V H) A.init *
        (prTrue_Q (fsInteractive A V H) A.init ^ 2 - (n : ℝ≥0∞)⁻¹) ≤
      prTrue_Q (QComp.qbind (rewindExtractWith M A H) fun o => QComp.qpure (e o)) A.init := by
  rw [rewindExtractWith_eq M V g hM e he A H]
  exact rewindExtract_bound A V H hV

end Extractor

end CatCrypt.Quantum.QROM
