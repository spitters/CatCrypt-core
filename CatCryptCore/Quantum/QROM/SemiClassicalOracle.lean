/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.OracleRegisterProbe
public import CatCryptCore.Quantum.TensorProduct
public import CatCryptCore.Quantum.Measurement

/-!
# The semi-classical oracle over `QComp`

The semi-classical oracle of Ambainis–Hamburg–Unruh (CRYPTO 2019, §2) for a
function `H : X → Y` and a set `S ⊆ X` measures whether the query register lies
in `S`, records the outcome, and then applies the standard oracle for `H`. The
event `Find` is that some measurement returned `true`. This module defines the
oracle, a `q`-query adversary with a work register, the two runs (standard and
semi-classical), their acceptance and `Find` probabilities, and proves the two
structural facts on which the O2H argument rests: the semi-classical oracle at
`S = ∅` is the standard oracle, and on the `Find = false` branch the run depends
on `H` only outside `S`.

The total register is `Fin (m * n * w)`: the query register `Fin (m * n)` of
`OracleRegisterProbe` (row-major over `Fin m × Fin n`) tensored with a work
register `Fin w`, so that `m * n * w` is syntactically `(m * n) * w` and the
oracle is `stdOracleFixedG m n H ⊗ₖ 1` at the type `TensorProduct.kronecker`
produces.

## Main definitions

* `oracleU m n w H`, `oracleQ m n w H` — the standard oracle for `H` on the
  total register, as a unitary and as a unitary channel
* `projS m n w S` — the projector `∑_{x ∈ S} |x⟩⟨x| ⊗ I_n ⊗ I_w`
* `measProj P` — the two-outcome projective measurement `{P, 1 - P}` as a
  `QComp d Bool`, outcome `true` for `P`
* `scOracleQ m n w H S` — the semi-classical oracle: measure `projS`, then
  apply `oracleQ H`, returning the measurement outcome
* `QAdv m n w q` — a `q`-query adversary: `q + 1` unitaries, an initial state
  and a final projector
* `run A H`, `runSC A H S` — the standard run and the semi-classical run, the
  latter returning `(output, find)`
* `prOut`, `prOutSC`, `prFind` — the acceptance and `Find` probabilities in
  `ℝ≥0∞`, through `prTrue_Q`

## Main results

* `kronecker_mem_unitaryGroup` — the Kronecker product of unitaries is unitary
* `projS_eq_diagonal`, `projS_mul_self`, `projS_conjTranspose`, `projS_isProj`
* `scOracleQ_empty`, `runSC_empty`, `prFind_empty` — at `S = ∅` the
  semi-classical run is the standard run with `find = false`
* `oracleU_mul_one_sub_projS` — `U_H (1 - Π_S) = U_{H'} (1 - Π_S)` when `H`
  and `H'` agree outside `S`
* `scOracleQ_branch_false_congr`, `runSC_branch_find_false_congr` — the
  `find = false` branch of the semi-classical run is the same for `H` and `H'`

## Scope

Modelled: a fixed-function oracle `H : Fin m → Fin n` as the symbolic
per-function unitary, one query register `Fin m × Fin n`, one work register
`Fin w`, an adversary alternating unitaries with oracle calls a fixed number of
times, and a classical output read by one final projective measurement. The
initial state is a field of the adversary, not an input to the run.

Not modelled: a function register (no `∑_G |G⟩` purification is reduced here),
an adaptive query count, auxiliary input beyond the adversary's initial state,
and mixed classical control between queries. The O2H bound itself is the next
module; this one provides the run-level identities it needs.

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], §2
* [Heidler, Unruh — Formalizing the O2H Lemma, CPP 2025]
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix Classical CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
  CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Branch lemmas for `qbind` over `Unit` and `Bool` -/

section Branch

variable {d : ℕ} {α β : Type}

/-- The branch of `qpure a` is the identity at `a` and zero elsewhere. -/
theorem qpure_branch_apply (a b : α) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (QComp.qpure a : QComp d α).branch b ρ = if b = a then ρ else 0 := by
  simp only [QComp.qpure]
  split_ifs <;> simp

/-- The branch of a bind over a `Unit`-valued prefix. -/
theorem qbind_unit_branch (I : QComp d Unit) (f : Unit → QComp d β) (b : β)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (QComp.qbind I f).branch b ρ = (f ()).branch b (I.branch () ρ) := by
  show ∑' u : Unit, (f u).branch b (I.branch u ρ) = _
  rw [tsum_eq_single () (fun u hu => absurd rfl hu)]

/-- The branch of a bind over a `Bool`-valued prefix, as the sum of the two
    outcome contributions. -/
theorem qbind_bool_branch (I : QComp d Bool) (f : Bool → QComp d β) (b : β)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (QComp.qbind I f).branch b ρ =
      (f false).branch b (I.branch false ρ) + (f true).branch b (I.branch true ρ) := by
  show ∑' u : Bool, (f u).branch b (I.branch u ρ) = _
  rw [tsum_fintype, Fintype.sum_bool, add_comm]

/-- Post-composing with a pure relabelling `g` whose image avoids `b` gives a
    zero branch at `b`. -/
theorem qbind_qpure_branch_of_ne (I : QComp d α) (g : α → β) (b : β)
    (hb : ∀ a, b ≠ g a) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (QComp.qbind I (fun a => QComp.qpure (g a))).branch b ρ = 0 := by
  show ∑' a, (QComp.qpure (g a) : QComp d β).branch b (I.branch a ρ) = 0
  simp only [qpure_branch_apply, hb, if_false, tsum_zero]

/-- The branch of a unitary channel is conjugation by the unitary. -/
theorem unitaryChannel_branch_apply (U : Matrix.unitaryGroup (Fin d) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (unitaryChannel U).branch () ρ = (U : Matrix (Fin d) (Fin d) ℂ) * ρ * (U : Matrix _ _ ℂ)ᴴ :=
  rfl

end Branch

/-! ## Kronecker products of unitaries -/

section Kronecker

variable {d₁ d₂ : ℕ}

/-- The Kronecker product of two unitaries is unitary. -/
theorem kronecker_mem_unitaryGroup {A : Matrix (Fin d₁) (Fin d₁) ℂ}
    {B : Matrix (Fin d₂) (Fin d₂) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin d₁) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin d₂) ℂ) :
    A ⊗ₖ B ∈ Matrix.unitaryGroup (Fin (d₁ * d₂)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA hB ⊢
  rw [star_eq_conjTranspose] at hA hB ⊢
  rw [conjTranspose_kronecker, kronecker_mul_kronecker, hA, hB, kronecker_one_one]

/-- A diagonal matrix tensored with the identity is diagonal, with the entry
    read off the first factor of the index. -/
theorem diagonal_kronecker_one (f : Fin d₁ → ℂ) :
    Matrix.diagonal f ⊗ₖ (1 : Matrix (Fin d₂) (Fin d₂) ℂ) =
      Matrix.diagonal (fun k => f ((finProdEquiv d₁ d₂).symm k).1) := by
  ext i j
  simp only [kronecker_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have : ¬(((finProdEquiv d₁ d₂).symm i).1 = ((finProdEquiv d₁ d₂).symm j).1 ∧
      ((finProdEquiv d₁ d₂).symm i).2 = ((finProdEquiv d₁ d₂).symm j).2) := by
      intro ⟨h1, h2⟩
      exact h ((finProdEquiv d₁ d₂).symm.injective (Prod.ext h1 h2))
    rcases not_and_or.mp this with h1 | h2
    · simp [h, h1]
    · simp [h, h2]

end Kronecker

/-! ## The two-outcome projective measurement -/

section MeasProj

variable {d : ℕ}

/-- The projective measurement `{P, 1 - P}` of a projector `P`, outcome `true`
    for `P`. -/
def projMeasurement (P : Matrix (Fin d) (Fin d) ℂ) (hH : Pᴴ = P) (hI : P * P = P) :
    ProjectiveMeasurement d Bool where
  op
    | true => P
    | false => 1 - P
  completeness := by
    rw [Fintype.sum_bool]
    simp only [hH, conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub, one_mul, mul_one, hI]
    abel
  self_adjoint b := by
    cases b <;> simp [hH]
  idempotent b := by
    cases b
    · simp only [sub_mul, mul_sub, one_mul, mul_one, hI]; abel
    · exact hI

/-- The measurement `{P, 1 - P}` as an instrument with a `Bool` outcome. -/
def measProj (P : Matrix (Fin d) (Fin d) ℂ) (hH : Pᴴ = P) (hI : P * P = P) :
    QComp d Bool :=
  projectiveMeasure (projMeasurement P hH hI)

theorem measProj_branch_true (P : Matrix (Fin d) (Fin d) ℂ) (hH : Pᴴ = P) (hI : P * P = P)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (measProj P hH hI).branch true ρ = P * ρ * Pᴴ := rfl

theorem measProj_branch_false (P : Matrix (Fin d) (Fin d) ℂ) (hH : Pᴴ = P) (hI : P * P = P)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (measProj P hH hI).branch false ρ = (1 - P) * ρ * (1 - P)ᴴ := rfl

end MeasProj

/-! ## The projector onto `S` on the total register -/

section Proj

variable (m n w : ℕ)

/-- The `Fin m` component of a total-register index. -/
def xPart (k : Fin (m * n * w)) : Fin m :=
  ((finProdEquiv m n).symm ((finProdEquiv (m * n) w).symm k).1).1

/-- The indicator of `S` on the query register's first factor. -/
def indS (S : Finset (Fin m)) (x : Fin m) : ℂ := if x ∈ S then 1 else 0

/-- The projector `∑_{x ∈ S} |x⟩⟨x| ⊗ I_n ⊗ I_w` onto the states whose query
    register lies in `S`. -/
def projS (S : Finset (Fin m)) : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ :=
  (Matrix.diagonal (indS m S) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)) ⊗ₖ
    (1 : Matrix (Fin w) (Fin w) ℂ)

theorem projS_eq_diagonal (S : Finset (Fin m)) :
    projS m n w S = Matrix.diagonal (fun k => indS m S (xPart m n w k)) := by
  unfold projS
  rw [diagonal_kronecker_one, diagonal_kronecker_one]
  rfl

theorem projS_mul_self (S : Finset (Fin m)) :
    projS m n w S * projS m n w S = projS m n w S := by
  rw [projS_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext k
  simp only [indS]; split_ifs <;> simp

theorem projS_conjTranspose (S : Finset (Fin m)) :
    (projS m n w S)ᴴ = projS m n w S := by
  rw [projS_eq_diagonal, Matrix.diagonal_conjTranspose]
  congr 1; funext k
  simp only [Pi.star_apply, indS]; split_ifs <;> simp

/-- `projS` is an orthogonal projector: idempotent and self-adjoint. -/
theorem projS_isProj (S : Finset (Fin m)) :
    projS m n w S * projS m n w S = projS m n w S ∧ (projS m n w S)ᴴ = projS m n w S :=
  ⟨projS_mul_self m n w S, projS_conjTranspose m n w S⟩

theorem projS_empty : projS m n w ∅ = 0 := by
  rw [projS_eq_diagonal]
  simp [indS]

end Proj

/-! ## The oracle on the total register -/

section Oracle

variable (m n w : ℕ) [NeZero n]

/-- The standard oracle for `H` on the total register `Fin (m * n * w)`:
    `stdOracleFixedG m n H ⊗ₖ 1` on `(query register) ⊗ (work register)`. -/
def oracleU (H : Fin m → Fin n) : Matrix.unitaryGroup (Fin (m * n * w)) ℂ :=
  ⟨stdOracleFixedG m n H ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ),
    kronecker_mem_unitaryGroup (stdOracleFixedG_unitary m n H)
      (Matrix.mem_unitaryGroup_iff.mpr (by simp))⟩

@[simp]
theorem oracleU_val (H : Fin m → Fin n) :
    (oracleU m n w H : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) =
      stdOracleFixedG m n H ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ) := rfl

/-- The standard oracle for `H` as a unitary channel on the total register. -/
def oracleQ (H : Fin m → Fin n) : QComp (m * n * w) Unit :=
  unitaryChannel (oracleU m n w H)

/-- The semi-classical oracle for `H` and `S`: measure `{Π_S, 1 - Π_S}`
    (outcome `true` iff the query register lies in `S`), then apply the
    standard oracle for `H`; the outcome is returned. -/
def scOracleQ (H : Fin m → Fin n) (S : Finset (Fin m)) : QComp (m * n * w) Bool :=
  QComp.qbind (measProj (projS m n w S) (projS_conjTranspose m n w S) (projS_mul_self m n w S))
    (fun b => QComp.qbind (oracleQ m n w H) (fun _ => QComp.qpure b))

theorem scOracleQ_branch_true (H : Fin m → Fin n) (S : Finset (Fin m))
    (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (scOracleQ m n w H S).branch true ρ =
      (oracleU m n w H : Matrix _ _ ℂ) * (projS m n w S * ρ * projS m n w S) *
        (oracleU m n w H : Matrix _ _ ℂ)ᴴ := by
  unfold scOracleQ
  rw [qbind_bool_branch, qbind_unit_branch, qbind_unit_branch, qpure_branch_apply,
    qpure_branch_apply, measProj_branch_true, measProj_branch_false, projS_conjTranspose]
  simp [oracleQ, unitaryChannel_branch_apply]

theorem scOracleQ_branch_false (H : Fin m → Fin n) (S : Finset (Fin m))
    (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (scOracleQ m n w H S).branch false ρ =
      (oracleU m n w H : Matrix _ _ ℂ) * ((1 - projS m n w S) * ρ * (1 - projS m n w S)) *
        (oracleU m n w H : Matrix _ _ ℂ)ᴴ := by
  unfold scOracleQ
  rw [qbind_bool_branch, qbind_unit_branch, qbind_unit_branch, qpure_branch_apply,
    qpure_branch_apply, measProj_branch_true, measProj_branch_false, conjTranspose_sub,
    conjTranspose_one, projS_conjTranspose]
  simp [oracleQ, unitaryChannel_branch_apply]

/-- At `S = ∅` the semi-classical oracle is the standard oracle with outcome
    `false`. -/
theorem scOracleQ_empty (H : Fin m → Fin n) :
    scOracleQ m n w H ∅ = QComp.qbind (oracleQ m n w H) (fun _ => QComp.qpure false) := by
  apply QComp.ext_fun; intro b ρ
  unfold scOracleQ
  rw [qbind_bool_branch, measProj_branch_true, measProj_branch_false, projS_empty]
  simp

end Oracle

/-! ## The oracle chain and the adversary -/

section Chain

variable {d : ℕ}

/-- `U₀ ; O ; U₁ ; … ; O ; U_q` for a `Unit`-valued oracle `O`. -/
def oracleChain (O : QComp d Unit) :
    (q : ℕ) → (Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) → QComp d Unit
  | 0, U => unitaryChannel (U 0)
  | q + 1, U =>
    QComp.qbind (unitaryChannel (U 0)) fun _ =>
      QComp.qbind O fun _ => oracleChain O q (Fin.tail U)

/-- `U₀ ; O ; U₁ ; … ; O ; U_q` for a `Bool`-valued oracle `O`, returning the
    disjunction of the oracle outcomes. -/
def scChain (O : QComp d Bool) :
    (q : ℕ) → (Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) → QComp d Bool
  | 0, U => QComp.qbind (unitaryChannel (U 0)) fun _ => QComp.qpure false
  | q + 1, U =>
    QComp.qbind (unitaryChannel (U 0)) fun _ =>
      QComp.qbind O fun b =>
        QComp.qbind (scChain O q (Fin.tail U)) fun f => QComp.qpure (b || f)

/-- A `Bool`-valued oracle that always returns `false` chains to the
    `Unit`-valued chain of its underlying channel. -/
theorem scChain_qbind_pure_false (O : QComp d Unit) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    scChain (QComp.qbind O fun _ => QComp.qpure false) q U =
      QComp.qbind (oracleChain O q U) fun _ => QComp.qpure false := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [scChain, oracleChain, ih, QComp.qbind_assoc, QComp.qpure_qbind, Bool.false_or]

/-- The `false` branch of `scChain` depends on the oracle only through its
    `false` branch. -/
theorem scChain_branch_false_congr (O O' : QComp d Bool)
    (h : O.branch false = O'.branch false) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    (scChain O q U).branch false = (scChain O' q U).branch false := by
  induction q with
  | zero => rfl
  | succ q ih =>
    apply LinearMap.ext; intro ρ
    simp only [scChain]
    simp only [qbind_unit_branch, qbind_bool_branch, qpure_branch_apply]
    simp [h, ih]

/-- A `q`-query adversary on the total register `Fin (m * n * w)`: the
    unitaries `U₀, …, U_q` between and around the `q` oracle calls, the initial
    state, and the final projector whose outcome `true` is the output `1`. -/
structure QAdv (m n w q : ℕ) where
  /-- The unitaries `U₀, …, U_q`. -/
  U : Fin (q + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ
  /-- The initial state. -/
  init : DensityMatrix (m * n * w)
  /-- The projector of the final measurement. -/
  final : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ
  final_conjTranspose : finalᴴ = final
  final_mul_self : final * final = final

end Chain

section Run

variable {m n w q : ℕ} [NeZero n]

/-- The final measurement of `A` as an instrument. -/
def QAdv.measure (A : QAdv m n w q) : QComp (m * n * w) Bool :=
  measProj A.final A.final_conjTranspose A.final_mul_self

/-- The standard run `U₀ ; O_H ; U₁ ; … ; O_H ; U_q ; measure`. -/
def run (A : QAdv m n w q) (H : Fin m → Fin n) : QComp (m * n * w) Bool :=
  QComp.qbind (oracleChain (oracleQ m n w H) q A.U) fun _ => A.measure

/-- The semi-classical run with `scOracleQ H S` in place of `O_H`, returning
    `(output, find)`; `find = true` iff some measurement returned `true`. -/
def runSC (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m)) :
    QComp (m * n * w) (Bool × Bool) :=
  QComp.qbind (scChain (scOracleQ m n w H S) q A.U) fun f =>
    QComp.qbind A.measure fun out => QComp.qpure (out, f)

/-- The probability that the standard run outputs `1`. -/
def prOut (A : QAdv m n w q) (H : Fin m → Fin n) : ℝ≥0∞ :=
  prTrue_Q (run A H) A.init

/-- The probability that the semi-classical run outputs `1`. -/
def prOutSC (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m)) : ℝ≥0∞ :=
  prTrue_Q (QComp.qbind (runSC A H S) fun p => QComp.qpure p.1) A.init

/-- The probability of `Find`: some semi-classical measurement returned `true`. -/
def prFind (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m)) : ℝ≥0∞ :=
  prTrue_Q (QComp.qbind (runSC A H S) fun p => QComp.qpure p.2) A.init

/-- At `S = ∅` the semi-classical run is the standard run with `find = false`. -/
theorem runSC_empty (A : QAdv m n w q) (H : Fin m → Fin n) :
    runSC A H ∅ = QComp.qbind (run A H) fun out => QComp.qpure (out, false) := by
  unfold runSC run
  rw [scOracleQ_empty, scChain_qbind_pure_false, QComp.qbind_assoc, QComp.qbind_assoc]
  congr 1; funext _
  rw [QComp.qpure_qbind]

/-- At `S = ∅` the `Find` probability is zero. -/
theorem prFind_empty (A : QAdv m n w q) (H : Fin m → Fin n) :
    prFind A H ∅ = 0 := by
  unfold prFind
  rw [runSC_empty, QComp.qbind_assoc]
  simp only [QComp.qpure_qbind]
  unfold prTrue_Q
  rw [qbind_qpure_branch_of_ne _ (fun _ => false) true (fun _ => by decide)]
  simp

/-- `U_H (1 - Π_S) = U_{H'} (1 - Π_S)` when `H` and `H'` agree outside `S`: on a
    basis ket whose query register lies outside `S` both oracles act as
    `|x, y, z⟩ ↦ |x, y + H x, z⟩`, and `1 - Π_S` annihilates the others. -/
theorem oracleU_mul_one_sub_projS (H H' : Fin m → Fin n) (S : Finset (Fin m))
    (hHH' : ∀ x, x ∉ S → H x = H' x) :
    (oracleU m n w H : Matrix _ _ ℂ) * (1 - projS m n w S) =
      (oracleU m n w H' : Matrix _ _ ℂ) * (1 - projS m n w S) := by
  rw [projS_eq_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_sub]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
  by_cases hx : xPart m n w j ∈ S
  · simp [indS, hx]
  · simp only [indS, hx, if_false, sub_zero, mul_one, oracleU_val, kronecker_apply]
    congr 1
    obtain ⟨⟨x, y⟩, hxy⟩ := (fixedIndex m n).surjective ((finProdEquiv (m * n) w).symm j).1
    have hx' : x = xPart m n w j := by
      unfold xPart
      rw [← hxy]
      show x = ((fixedIndex m n).symm (fixedIndex m n (x, y))).1
      rw [Equiv.symm_apply_apply]
    have hcol : ∀ K : Fin m → Fin n, ∀ i : Fin (m * n),
        stdOracleFixedG m n K i (fixedIndex m n (x, y)) =
          (Pi.single (fixedIndex m n (x, y + K x)) (1 : ℂ) : Fin (m * n) → ℂ) i := by
      intro K i
      have := congrFun (stdOracleFixedG_ket m n K x y) i
      rwa [Matrix.mulVec_single_one] at this
    rw [← hxy, hcol, hcol, hHH' x (hx' ▸ hx)]

/-- The `false` branch of the semi-classical oracle is the same for two
    functions that agree outside `S`. -/
theorem scOracleQ_branch_false_congr (H H' : Fin m → Fin n) (S : Finset (Fin m))
    (hHH' : ∀ x, x ∉ S → H x = H' x) :
    (scOracleQ m n w H S).branch false = (scOracleQ m n w H' S).branch false := by
  apply LinearMap.ext; intro ρ
  rw [scOracleQ_branch_false, scOracleQ_branch_false]
  have hP : (1 - projS m n w S)ᴴ = 1 - projS m n w S := by
    rw [conjTranspose_sub, conjTranspose_one, projS_conjTranspose]
  have key : ∀ K : Fin m → Fin n,
      (oracleU m n w K : Matrix _ _ ℂ) * ((1 - projS m n w S) * ρ * (1 - projS m n w S)) *
        (oracleU m n w K : Matrix _ _ ℂ)ᴴ =
      ((oracleU m n w K : Matrix _ _ ℂ) * (1 - projS m n w S)) * ρ *
        ((oracleU m n w K : Matrix _ _ ℂ) * (1 - projS m n w S))ᴴ := by
    intro K
    rw [conjTranspose_mul, hP]
    simp only [Matrix.mul_assoc]
  rw [key, key, oracleU_mul_one_sub_projS H H' S hHH']

/-- The `find = false` branch of the semi-classical run is the same for two
    functions that agree outside `S` (AHU, CRYPTO 2019, the punctured-oracle
    step). -/
theorem runSC_branch_find_false_congr (A : QAdv m n w q) (H H' : Fin m → Fin n)
    (S : Finset (Fin m)) (hHH' : ∀ x, x ∉ S → H x = H' x) (out : Bool) :
    (runSC A H S).branch (out, false) = (runSC A H' S).branch (out, false) := by
  apply LinearMap.ext; intro ρ
  have hsc := scChain_branch_false_congr _ _ (scOracleQ_branch_false_congr H H' S hHH') q A.U
  unfold runSC
  simp only [qbind_bool_branch, qpure_branch_apply]
  simp [Prod.ext_iff, hsc]

end Run

end CatCrypt.Quantum.QROM
