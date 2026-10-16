/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.Rewinding

/-!
# Fiat–Shamir for Σ-protocols in the quantum random-oracle model

A Σ-protocol for a relation `rel : Stmt → Wit → Prop` encoded on the registers
of a prover `QAdv m n w q`: the commitment register value `x : Fin m` is the
commitment, the challenge `θ : Fin n` the challenge, and the work register value
`k : Fin w` decodes to the response `resp k`. The verifier `sigmaQV S st` is the
diagonal projector onto the basis states whose response is accepted by the
classical test `verify st x θ`.

The encoding carries two properties of the protocol: unique responses (for each
statement, commitment and challenge at most one response is accepted) and special
soundness (two accepted transcripts with one commitment and distinct challenges
give a witness through `extract`).

With unique responses the accept outcome of the measurement of the response is
the verifier measurement, so Unruh's rewinding extractor with response
measurements `rewindExtractWith (sigmaRespMeas S st)` satisfies the rewinding
bound `rewindExtractWith_bound`. Composed with the measure-and-reprogram bound
of Don, Fehr, Majenz and Schaffner, `fiatShamir_random_oracle_interactive`, and
with special soundness, it gives the reduction `fiatShamir_sigma_qrom` from the
Fiat–Shamir success probability of a prover family to the probability that the
extractor `sigmaExtractor S A` outputs a witness of its statement. If the
relation is hard on the statement distribution, the right-hand side is small.

## Main definitions

* `diagB f`, `clsMeas cls` — diagonal projectors and measurements of
  classifications of the computational basis
* `SigmaQEnc Stmt Wit rel Resp m n w` — the encoding of a Σ-protocol with unique
  responses and special soundness
* `sigmaQV S st` — the verifier projectors of the statement `st`
* `sigmaRespMeas S st x θ` — the measurement of the accept outcome and the
  response
* `SigmaQEnc.twoAccept`, `SigmaQEnc.witness` — two accepted transcripts with
  distinct challenges, and the witness extracted from them
* `QRelAdv Stmt Wit d`, `relAdvantage rel gen B` — witness-finding programs and
  their success probability on a uniform statement `gen i`
* `sigmaExtractor S A` — the extractor of a prover family
* `fsAdvantage S gen A` — the Fiat–Shamir success probability over a uniform
  statement and a uniform oracle

## Main results

* `sigmaRespMeas_qbind_outAcc` — the accept outcome of the response measurement
  is the verifier measurement
* `sigma_rewinding_extractable` — Unruh's rewinding lemma for the extractor
* `twoAccept_rel_witness` — special soundness on the extractor's outcomes
* `fiatShamir_sigma_qrom` —
  `(fsAdvantage S gen A / (2q + 1)²)³ ≤ relAdvantage rel gen (sigmaExtractor S A) + 1/n`

## References

* [Unruh — Quantum Proofs of Knowledge, EUROCRYPT 2012], Lemma 7
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

/-! ## Measurements in the computational basis -/

section Basis

variable {d : ℕ}

/-- The diagonal projector onto the basis states on which `f` holds. -/
def diagB (f : Fin d → Bool) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun k => if f k then 1 else 0

theorem diagB_conjTranspose (f : Fin d → Bool) : (diagB f)ᴴ = diagB f := by
  rw [diagB, Matrix.diagonal_conjTranspose]
  congr 1; funext k
  simp only [Pi.star_apply]; split_ifs <;> simp

theorem diagB_mul_self (f : Fin d → Bool) : diagB f * diagB f = diagB f := by
  rw [diagB, Matrix.diagonal_mul_diagonal]
  congr 1; funext k
  split_ifs <;> simp

theorem sum_diagB_eq_one {α : Type} [Fintype α] [DecidableEq α] (cls : Fin d → α) :
    ∑ a, diagB (fun k => decide (cls k = a)) = 1 := by
  ext i j
  simp only [diagB, Matrix.sum_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- The measurement of the classification `cls` of the basis states: the
    outcome `a` projects onto the basis states `k` with `cls k = a`. -/
def clsMeas {α : Type} [Fintype α] [DecidableEq α] (cls : Fin d → α) :
    ProjectiveMeasurement d α where
  op a := diagB fun k => decide (cls k = a)
  completeness := by
    simp only [diagB_conjTranspose, diagB_mul_self]
    exact sum_diagB_eq_one cls
  self_adjoint a := diagB_conjTranspose _
  idempotent a := diagB_mul_self _

theorem clsMeas_branch {α : Type} [Fintype α] [DecidableEq α] (cls : Fin d → α) (a : α)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (projectiveMeasure (clsMeas cls)).branch a ρ =
      diagB (fun k => decide (cls k = a)) * ρ * (diagB fun k => decide (cls k = a))ᴴ :=
  rfl

theorem diagB_eq_zero {f : Fin d → Bool} (h : ∀ k, f k = false) : diagB f = 0 := by
  rw [diagB, ← Matrix.diagonal_zero]
  congr 1; funext k
  simp [h k]

/-- Relabelling the outcomes of `clsMeas cls` by `g` is the measurement of the
    classification `g ∘ cls`, when `g ∘ cls` determines `cls` (the basis states
    of one `g`-value lie in one class). -/
theorem clsMeas_qbind_qpure {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (cls : Fin d → α) (g : α → β) (hU : ∀ k k', g (cls k) = g (cls k') → cls k = cls k') :
    QComp.qbind (projectiveMeasure (clsMeas cls)) (fun a => QComp.qpure (g a)) =
      projectiveMeasure (clsMeas fun k => g (cls k)) := by
  apply QComp.ext_fun; intro b ρ
  rw [qbind_branch_apply, tsum_fintype]
  simp only [qpure_branch_apply, clsMeas_branch]
  by_cases hb : ∃ k₀, g (cls k₀) = b
  · obtain ⟨k₀, hk₀⟩ := hb
    rw [Finset.sum_eq_single (cls k₀)]
    · rw [if_pos hk₀.symm]
      have e : (fun k => decide (cls k = cls k₀)) = fun k => decide (g (cls k) = b) := by
        funext k
        refine decide_eq_decide.mpr ⟨fun h => h ▸ hk₀, fun h => hU _ _ (h.trans hk₀.symm)⟩
      rw [e]
    · intro a _ ha
      split_ifs with hga
      · rw [diagB_eq_zero fun k => decide_eq_false fun (h : cls k = a) => ha (h.symm.trans
          (hU _ _ ((congrArg g h).trans (hga.symm.trans hk₀.symm))))]
        simp
      · rfl
    · exact fun h => absurd (Finset.mem_univ _) h
  · push Not at hb
    rw [diagB_eq_zero fun k => decide_eq_false (hb k)]
    simp only [Matrix.zero_mul]
    refine Finset.sum_eq_zero fun a _ => ?_
    split_ifs with hga
    · rw [diagB_eq_zero fun k => decide_eq_false fun (h : cls k = a) =>
        hb k ((congrArg g h).trans hga.symm)]
      simp
    · rfl

/-- The measurement of a `Bool` classification `f` is the two-outcome
    measurement of `diagB f`. -/
theorem clsMeas_bool_eq_measProj (f : Fin d → Bool) :
    projectiveMeasure (clsMeas f) = measProj (diagB f) (diagB_conjTranspose f) (diagB_mul_self f) := by
  have h1 : (diagB fun k => decide (f k = true)) = diagB f := by
    simp only [Bool.decide_eq_true]
  have h0 : (diagB fun k => decide (f k = false)) = 1 - diagB f := by
    ext i j
    simp only [diagB, Matrix.diagonal_apply, Matrix.sub_apply, Matrix.one_apply]
    split_ifs <;> simp_all
  apply QComp.ext_fun; intro b ρ
  cases b
  · rw [measProj_branch_false, ← h0]; rfl
  · rw [measProj_branch_true, ← h1]; rfl

end Basis

/-! ## Uniform averages in `ℝ≥0∞` -/

section Avg

/-- Jensen's inequality for the cube of a uniform average. -/
theorem avg_pow_three_le {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ≥0∞) :
    ((Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i, f i) ^ 3 ≤ (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i, f i ^ 3 := by
  have hc0 : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hw : ∑ _i : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ENNReal.mul_inv_cancel hc0 (ENNReal.natCast_ne_top _)]
  have h := ENNReal.rpow_arith_mean_le_arith_mean_rpow Finset.univ
    (fun _ => (Fintype.card ι : ℝ≥0∞)⁻¹) f hw (p := 3) (by norm_num)
  simp only [← Finset.mul_sum] at h
  exact_mod_cast h

/-- A uniform average of `f i + b` is the average of `f` plus `b`. -/
theorem avg_add_const {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ≥0∞) (b : ℝ≥0∞) :
    (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i, (f i + b) = (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i, f i + b := by
  have hc0 : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, ENNReal.inv_mul_cancel hc0 (ENNReal.natCast_ne_top _), one_mul]

end Avg

/-! ## The encoding of a Σ-protocol and its verifier -/

section Verifier

variable {Stmt Wit : Type} {rel : Stmt → Wit → Prop} {Resp : Type} {m n w : ℕ}

/-- A Σ-protocol for the relation `rel` encoded on the register `Fin (m * n * w)`:
    the commitment is the commitment register value `x : Fin m`, the challenge is
    `θ : Fin n`, and the work register value `k : Fin w` encodes the response
    `resp k`. The classical test `verify st x θ z` accepts the response `z` to the
    challenge `θ` on the commitment `x` for the statement `st`. Responses are
    unique, and `extract` is a special-soundness extractor. -/
structure SigmaQEnc (Stmt Wit : Type) (rel : Stmt → Wit → Prop) (Resp : Type) (m n w : ℕ) where
  /-- The response encoded by the work register. -/
  resp : Fin w → Resp
  /-- The verifier's test of a transcript for a statement. -/
  verify : Stmt → Fin m → Fin n → Resp → Bool
  /-- The special-soundness extractor on two transcripts with one commitment. -/
  extract : Stmt → Fin m → Fin n → Resp → Fin n → Resp → Wit
  /-- Unique responses: at most one response is accepted for a statement, a
      commitment and a challenge. -/
  unique_resp : ∀ st x θ z z', verify st x θ z = true → verify st x θ z' = true → z = z'
  /-- Special soundness: two accepted transcripts with one commitment and distinct
      challenges give a witness through `extract`. -/
  special_sound : ∀ st x θ z θ' z', verify st x θ z = true → verify st x θ' z' = true →
    θ ≠ θ' → rel st (extract st x θ z θ' z')

/-- The work register component of a total-register index. -/
def wPart (k : Fin (m * n * w)) : Fin w := ((finProdEquiv (m * n) w).symm k).2

/-- The basis state `k` carries a response accepted for the statement `st`, the
    commitment `x` and the challenge `θ`. -/
def SigmaQEnc.accK (S : SigmaQEnc Stmt Wit rel Resp m n w) (st : Stmt) (x : Fin m) (θ : Fin n)
    (k : Fin (m * n * w)) : Bool :=
  S.verify st x θ (S.resp (wPart k))

/-- The verifier of the statement `st`: `V(x, θ)` projects onto the basis states
    whose response is accepted for `st`, `x` and `θ`. -/
def sigmaQV (S : SigmaQEnc Stmt Wit rel Resp m n w) (st : Stmt) : QVerifier m n w where
  proj x θ := diagB (S.accK st x θ)
  proj_conjTranspose _ _ := diagB_conjTranspose _
  proj_mul_self _ _ := diagB_mul_self _

/-- The verifier projectors are diagonal, so they commute with the projectors of
    the commitment measurement. -/
theorem sigmaQV_proj_comm (S : SigmaQEnc Stmt Wit rel Resp m n w) (st : Stmt) (x : Fin m)
    (θ : Fin n) (x' : Fin m) :
    (sigmaQV S st).proj x θ * projS m n w {x'} = projS m n w {x'} * (sigmaQV S st).proj x θ := by
  show diagB _ * _ = _ * diagB _
  rw [projS_eq_diagonal, diagB, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext k
  exact mul_comm _ _

variable [Fintype Resp] [DecidableEq Resp]

/-- The measurement of the accept outcome and the response for the statement
    `st`, the commitment `x` and the challenge `θ`: `some z` on the accepting basis
    states with response `z`, `none` on the rejecting ones. -/
def sigmaRespMeas (S : SigmaQEnc Stmt Wit rel Resp m n w) (st : Stmt) (x : Fin m) (θ : Fin n) :
    QComp (m * n * w) (Option Resp) :=
  projectiveMeasure (clsMeas fun k => if S.accK st x θ k then some (S.resp (wPart k)) else none)

/-- An outcome of `sigmaRespMeas S st x θ` is accepted: it is a response accepted
    for `st`, `x` and `θ`. -/
def SigmaQEnc.outAcc (S : SigmaQEnc Stmt Wit rel Resp m n w) (st : Stmt) (x : Fin m) (θ : Fin n) :
    Option Resp → Bool
  | some z => S.verify st x θ z
  | none => false

/-- The accept outcome of the response measurement is the verifier measurement:
    all accepting basis states carry the same response, by unique responses. -/
theorem sigmaRespMeas_qbind_outAcc (S : SigmaQEnc Stmt Wit rel Resp m n w) (st : Stmt) (x : Fin m)
    (θ : Fin n) :
    QComp.qbind (sigmaRespMeas S st x θ) (fun o => QComp.qpure (S.outAcc st x θ o)) =
      measProj ((sigmaQV S st).proj x θ) ((sigmaQV S st).proj_conjTranspose x θ)
        ((sigmaQV S st).proj_mul_self x θ) := by
  have hg : (fun k => S.outAcc st x θ
      (if S.accK st x θ k then some (S.resp (wPart k)) else none)) = S.accK st x θ := by
    funext k
    by_cases h : S.accK st x θ k
    · rw [if_pos h, h]; exact h
    · rw [if_neg h, Bool.eq_false_iff.mpr h]; rfl
  unfold sigmaRespMeas
  rw [clsMeas_qbind_qpure _ _ ?_, hg]
  · exact clsMeas_bool_eq_measProj _
  · intro k k' hkk'
    have e : ∀ k, S.outAcc st x θ
        (if S.accK st x θ k then some (S.resp (wPart k)) else none) = S.accK st x θ k :=
      fun k => congrFun hg k
    rw [e, e] at hkk'
    by_cases h : S.accK st x θ k
    · have h' : S.accK st x θ k' = true := hkk' ▸ h
      rw [if_pos h, if_pos h']
      exact congrArg some (S.unique_resp st x θ _ _ h h')
    · have h' : ¬S.accK st x θ k' = true := hkk' ▸ h
      rw [if_neg h, if_neg h']

end Verifier

/-! ## The rewinding extractor and special soundness -/

section Extractor

variable {Stmt Wit : Type} {rel : Stmt → Wit → Prop} {Resp : Type} {m n w q : ℕ}

/-- Two accepted transcripts with the same commitment and distinct challenges for
    the statement `st`. -/
def SigmaQEnc.twoAccept (S : SigmaQEnc Stmt Wit rel Resp m n w) (st : Stmt) :
    Fin m × (Fin n × Option Resp) × (Fin n × Option Resp) → Bool
  | (x, (θ₁, some z₁), (θ₂, some z₂)) =>
    S.verify st x θ₁ z₁ && S.verify st x θ₂ z₂ && decide (θ₁ ≠ θ₂)
  | _ => false

/-- The special-soundness extractor applied to the outcomes of the rewinding
    extractor; `default` when a response is missing. -/
def SigmaQEnc.witness [Inhabited Wit] (S : SigmaQEnc Stmt Wit rel Resp m n w) (st : Stmt) :
    Fin m × (Fin n × Option Resp) × (Fin n × Option Resp) → Wit
  | (x, (θ₁, some z₁), (θ₂, some z₂)) => S.extract st x θ₁ z₁ θ₂ z₂
  | _ => default

/-- `twoAccept` reads the outcomes of the extractor through `outAcc`. -/
theorem SigmaQEnc.twoAccept_eq (S : SigmaQEnc Stmt Wit rel Resp m n w) (st : Stmt) (x : Fin m)
    (θ₁ : Fin n) (o₁ : Option Resp) (θ₂ : Fin n) (o₂ : Option Resp) :
    S.twoAccept st (x, (θ₁, o₁), (θ₂, o₂)) =
      (S.outAcc st x θ₁ o₁ && S.outAcc st x θ₂ o₂ && decide (θ₁ ≠ θ₂)) := by
  cases o₁ <;> cases o₂ <;> simp [SigmaQEnc.twoAccept, SigmaQEnc.outAcc]

/-- Special soundness on the extractor's outcomes: two accepted transcripts with
    distinct challenges give a witness of the statement. -/
theorem twoAccept_rel_witness [Inhabited Wit] (S : SigmaQEnc Stmt Wit rel Resp m n w)
    (st : Stmt) (o : Fin m × (Fin n × Option Resp) × (Fin n × Option Resp))
    (h : S.twoAccept st o = true) : rel st (S.witness st o) := by
  obtain ⟨x, ⟨θ₁, o₁⟩, ⟨θ₂, o₂⟩⟩ := o
  cases o₁ with
  | none => simp [SigmaQEnc.twoAccept] at h
  | some z₁ =>
    cases o₂ with
    | none => simp [SigmaQEnc.twoAccept] at h
    | some z₂ =>
      simp only [SigmaQEnc.twoAccept, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h₁, h₂⟩, hne⟩ := h
      exact S.special_sound st x θ₁ z₁ θ₂ z₂ h₁ h₂ hne

variable [Fintype Resp] [DecidableEq Resp] [NeZero n]

/-- Unruh's rewinding extractor for the statement `st`: `rewindExtractWith` with
    the measurements `sigmaRespMeas S st` of the accept outcome and the response.
    It runs the prover `A` once up to the measurement of the commitment and the
    response unitary twice, with one rewinding by its inverse between them. -/
def sigmaRewind (S : SigmaQEnc Stmt Wit rel Resp m n w) (st : Stmt) (A : QAdv m n w q)
    (H : Fin m → Fin n) :
    QComp (m * n * w) (Fin m × (Fin n × Option Resp) × (Fin n × Option Resp)) :=
  rewindExtractWith (sigmaRespMeas S st) A H

/-- **Unruh's rewinding lemma** (EUROCRYPT 2012, "Quantum Proofs of Knowledge",
    Lemma 7) for a Σ-protocol with unique responses. For the interactive game with
    acceptance probability `p = prTrue_Q (fsInteractive A (sigmaQV S st) H) A.init`,
    the extractor `sigmaRewind S st A H` outputs two accepted transcripts with
    distinct challenges with probability at least `p · (p² − 1/n)`. -/
theorem sigma_rewinding_extractable (S : SigmaQEnc Stmt Wit rel Resp m n w) (st : Stmt)
    (A : QAdv m n w q) (H : Fin m → Fin n) :
    prTrue_Q (fsInteractive A (sigmaQV S st) H) A.init *
        (prTrue_Q (fsInteractive A (sigmaQV S st) H) A.init ^ 2 - (n : ℝ≥0∞)⁻¹) ≤
      prTrue_Q (QComp.qbind (sigmaRewind S st A H) fun o => QComp.qpure (S.twoAccept st o))
        A.init :=
  rewindExtractWith_bound (sigmaRespMeas S st) (sigmaQV S st) (S.outAcc st)
    (sigmaRespMeas_qbind_outAcc S st) (S.twoAccept st) (S.twoAccept_eq st)
    (sigmaQV_proj_comm S st) A H

/-- The cube of the interactive acceptance probability is at most the probability
    that the extractor's witness is a witness of `st`, plus `1/n`. -/
theorem prTrue_fsInteractive_pow_three_le_rel [Inhabited Wit]
    (S : SigmaQEnc Stmt Wit rel Resp m n w) (st : Stmt) (A : QAdv m n w q) (H : Fin m → Fin n) :
    prTrue_Q (fsInteractive A (sigmaQV S st) H) A.init ^ 3 ≤
      prTrue_Q (QComp.qbind (sigmaRewind S st A H) fun o =>
          QComp.qpure (decide (rel st (S.witness st o)))) A.init + (n : ℝ≥0∞)⁻¹ := by
  have hp1 : prTrue_Q (fsInteractive A (sigmaQV S st) H) A.init ≤ 1 := by
    unfold prTrue_Q
    refine ENNReal.ofReal_le_one.mpr ((branch_true_trace_re_le _ _ A.init.psd).trans ?_)
    rw [A.init.tr_one, Complex.one_re]
  set p := prTrue_Q (fsInteractive A (sigmaQV S st) H) A.init
  have hext := (sigma_rewinding_extractable S st A H).trans
    (prTrue_Q_qbind_decide_mono _ (S.twoAccept st) (fun o => decide (rel st (S.witness st o)))
      (fun o ho => decide_eq_true (twoAccept_rel_witness S st o ho)) _)
  calc p ^ 3 = p * p ^ 2 := by ring
    _ ≤ p * ((p ^ 2 - (n : ℝ≥0∞)⁻¹) + (n : ℝ≥0∞)⁻¹) := by gcongr; exact le_tsub_add
    _ = p * (p ^ 2 - (n : ℝ≥0∞)⁻¹) + p * (n : ℝ≥0∞)⁻¹ := mul_add _ _ _
    _ ≤ _ := add_le_add hext (mul_le_of_le_one_left zero_le hp1)

end Extractor

/-! ## The reduction to the relation -/

section Reduction

variable {Stmt Wit : Type} {rel : Stmt → Wit → Prop} {Resp : Type} [Fintype Resp]
  [DecidableEq Resp] {m n w q : ℕ}

/-- A quantum witness-finding program on `Fin d`: on the statement `st` it starts
    from `init st` and outputs a candidate witness. -/
structure QRelAdv (Stmt Wit : Type) (d : ℕ) where
  /-- The initial state on the statement `st`. -/
  init : Stmt → DensityMatrix d
  /-- The program on the statement `st`. -/
  run : Stmt → QComp d Wit

/-- The probability that `B` outputs a witness of the statement `gen i` for a
    uniform index `i`. -/
def relAdvantage {ι : Type} [Fintype ι] {d : ℕ} (rel : Stmt → Wit → Prop) (gen : ι → Stmt)
    (B : QRelAdv Stmt Wit d) : ℝ≥0∞ :=
  (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i,
    prTrue_Q (QComp.qbind (B.run (gen i)) fun s => QComp.qpure (decide (rel (gen i) s)))
      (B.init (gen i))

variable [NeZero n] [Inhabited Wit]

/-- The extractor of a family of provers `A st`: a uniform oracle `H`, Unruh's
    rewinding extractor `sigmaRewind`, and the special-soundness extractor. It runs
    the prover `A st` once up to its commitment and its response unitary twice,
    rewinding once by the inverse of the response unitary; it adds two uniform
    challenges, two measurements of the response and one evaluation of
    `extract`. -/
def sigmaExtractor (S : SigmaQEnc Stmt Wit rel Resp m n w) (A : Stmt → QAdv m n w q) :
    QRelAdv Stmt Wit (m * n * w) where
  init st := (A st).init
  run st := QComp.qbind (uniformQ (Fin m → Fin n)) fun H =>
    QComp.qbind (sigmaRewind S st (A st) H) fun o => QComp.qpure (S.witness st o)

/-- The Fiat–Shamir success probability of the provers `A st`: over a uniform
    statement `gen i` and a uniform oracle `H`, `A^H` outputs a commitment `x`
    accepted by `V(x, H x)`. -/
def fsAdvantage {ι : Type} [Fintype ι] (S : SigmaQEnc Stmt Wit rel Resp m n w) (gen : ι → Stmt)
    (A : Stmt → QAdv m n w q) : ℝ≥0∞ :=
  (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i,
    (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ * ∑ H : Fin m → Fin n, ∑ x,
      prOutAt ((A (gen i)).withVerifier (sigmaQV S (gen i)) x (H x)) H x

/-- The success probability of `sigmaExtractor S A` on `st` is the average over the
    oracle of the probability that the rewinding extractor's witness is a witness
    of `st`. -/
theorem sigmaExtractor_success (S : SigmaQEnc Stmt Wit rel Resp m n w) (A : Stmt → QAdv m n w q)
    (st : Stmt) :
    prTrue_Q (QComp.qbind ((sigmaExtractor S A).run st) fun s =>
        QComp.qpure (decide (rel st s))) ((sigmaExtractor S A).init st) =
      (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ * ∑ H : Fin m → Fin n,
        prTrue_Q (QComp.qbind (sigmaRewind S st (A st) H) fun o =>
          QComp.qpure (decide (rel st (S.witness st o)))) (A st).init := by
  simp only [sigmaExtractor, QComp.qbind_assoc, QComp.qpure_qbind]
  exact prTrue_Q_uniformQ_bind _ _

/-- **Fiat–Shamir for Σ-protocols in the quantum random-oracle model.** For a
    Σ-protocol with unique responses and special soundness, every statement
    distribution `gen` on a uniform index and every family of `q`-query provers
    `A st`, the Fiat–Shamir success probability divided by `(2q + 1)²` (the
    measure-and-reprogram loss, DFMS19 Theorem 2), cubed (the rewinding loss,
    Unruh 2012 Lemma 7), is at most the probability that the extractor
    `sigmaExtractor S A` outputs a witness of its statement, plus `1/n`. -/
theorem fiatShamir_sigma_qrom {ι : Type} [Fintype ι] [Nonempty ι]
    (S : SigmaQEnc Stmt Wit rel Resp m n w) (gen : ι → Stmt) (A : Stmt → QAdv m n w q) :
    (fsAdvantage S gen A / ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2) ^ 3 ≤
      relAdvantage rel gen (sigmaExtractor S A) + (n : ℝ≥0∞)⁻¹ := by
  set N2 : ℝ≥0∞ := ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2
  set cS : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞)⁻¹
  set cH : ℝ≥0∞ := (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹
  set pr : ι → (Fin m → Fin n) → ℝ≥0∞ := fun i H =>
    prTrue_Q (fsInteractive (A (gen i)) (sigmaQV S (gen i)) H) (A (gen i)).init
  have hFS : fsAdvantage S gen A / N2 ≤ cS * ∑ i, cH * ∑ H, pr i H := by
    refine ENNReal.div_le_of_le_mul ?_
    rw [mul_assoc, Finset.sum_mul]
    refine mul_le_mul_right (Finset.sum_le_sum fun i _ => ?_) _
    exact (fiatShamir_random_oracle_interactive (A (gen i)) (sigmaQV S (gen i))).trans_eq
      (mul_comm _ _)
  calc (fsAdvantage S gen A / N2) ^ 3
      ≤ (cS * ∑ i, cH * ∑ H, pr i H) ^ 3 := by gcongr
    _ ≤ cS * ∑ i, (cH * ∑ H, pr i H) ^ 3 := avg_pow_three_le _
    _ ≤ cS * ∑ i, cH * ∑ H, pr i H ^ 3 := by
        gcongr with i
        exact avg_pow_three_le _
    _ ≤ cS * ∑ i, cH * ∑ H, (prTrue_Q (QComp.qbind (sigmaRewind S (gen i) (A (gen i)) H)
          fun o => QComp.qpure (decide (rel (gen i) (S.witness (gen i) o))))
            (A (gen i)).init + (n : ℝ≥0∞)⁻¹) := by
        gcongr with i _ H _
        exact prTrue_fsInteractive_pow_three_le_rel S (gen i) (A (gen i)) H
    _ = relAdvantage rel gen (sigmaExtractor S A) + (n : ℝ≥0∞)⁻¹ := by
        rw [relAdvantage]
        simp only [sigmaExtractor_success, cS, cH, avg_add_const]

end Reduction

end CatCrypt.Quantum.QROM
