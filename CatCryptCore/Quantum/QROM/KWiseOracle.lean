/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.O2HTheorem
public import CatCryptCore.Quantum.QROM.PermUnitaryCore

/-!
# A `q`-query adversary cannot distinguish a `2q`-wise independent oracle

Zhandry (CRYPTO 2012, Theorem 6.1): the acceptance probability of a `q`-query
quantum algorithm, averaged over a distribution on oracle tables, depends only
on the distribution's marginals on sets of at most `2q` points. In particular a
`2q`-wise independent distribution gives the same average as the uniform one.

The argument is by locality. A function `F` of the table `H : α → β` depends on
at most `k` points if it is a finite sum of functions each of which reads `H`
only on a set of at most `k` points. The class is closed under sums, conjugation
and products (with the bounds adding). Every entry of the oracle unitary reads
one table value, so every entry of the chain operator `runOp A H` depends on at
most `q` points, and the acceptance probability, a trace of
`X ρ Xᴴ` with `X = final * runOp A H`, depends on at most `2q` points. Two weights
on tables whose masses agree on every cylinder of at most `k` points give the
same average to every function that depends on at most `k` points.

## Main definitions

* `LocalOn S g` — `g` reads the table only on `S`
* `DependsOnAtMost k F` — `F` is a finite sum of functions each local on a set
  of at most `k` points
* `EntriesDependOnAtMost k M` — every entry of the matrix-valued `M` depends on
  at most `k` points
* `CylinderAgree k μ ν` — `μ` and `ν` give equal mass to every set of tables
  fixed on at most `k` points
* `KWiseIndep k μ` — `μ` agrees with the uniform weight on every cylinder of at
  most `k` points
* `prOutC A H` — the acceptance probability of the standard run as a complex
  trace

## Main results

* `DependsOnAtMost.add`, `.sum`, `.mul`, `.star`, `.mono` — closure properties
* `EntriesDependOnAtMost.mul`, `.conjTranspose` — closure under matrix product
  and conjugate transpose
* `oracleU_entries_dependsOn` — every entry of the oracle unitary reads one
  table value
* `chainOp_entries_dependsOn` — the chain operator with `q` oracle calls has
  entries depending on at most `q` points
* `prOutC_dependsOn` — the acceptance probability depends on at most `2q` points
* `sum_mul_eq_of_cylinderAgree` — cylinder-agreeing weights give equal averages
  to functions depending on at most `k` points
* `prOut_avg_eq_of_cylinderAgree`, `prOut_avg_eq_of_kWise` — the average
  acceptance probability of a `q`-query adversary under a `2q`-wise independent
  weight equals its average under the uniform weight

## Scope

The adversary is `QAdv` of `SemiClassicalOracle`: a fixed number of standard
oracle calls interleaved with fixed unitaries, an arbitrary initial density
matrix and a final projective measurement. Weights are arbitrary non-negative
functions on tables; no normalisation is required. The construction of a
`2q`-wise independent family (for example low-degree polynomials over a finite
field) and its efficient evaluation are not part of this module.

## References

* [Zhandry — Secure Identity-Based Encryption in the Quantum Random Oracle
  Model, CRYPTO 2012], Theorem 6.1
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal NNReal
open Matrix CatCrypt.Quantum

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Functions of a table that depend on few points -/

section Depends

variable {α β : Type}

/-- `g` reads the table `H` only on the points of `S`. -/
def LocalOn (S : Finset α) (g : (α → β) → ℂ) : Prop :=
  ∀ H H' : α → β, (∀ x ∈ S, H x = H' x) → g H = g H'

theorem LocalOn.mono {S T : Finset α} {g : (α → β) → ℂ} (h : LocalOn S g) (hST : S ⊆ T) :
    LocalOn T g :=
  fun H H' hH => h H H' fun x hx => hH x (hST hx)

/-- `F` is a finite sum of functions each of which reads the table on at most
    `k` points. -/
def DependsOnAtMost (k : ℕ) (F : (α → β) → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (S : ι → Finset α) (g : ι → (α → β) → ℂ),
    (∀ i, (S i).card ≤ k ∧ LocalOn (S i) (g i)) ∧ ∀ H, F H = ∑ i, g i H

namespace DependsOnAtMost

theorem of_localOn {k : ℕ} {S : Finset α} {g : (α → β) → ℂ} (hS : S.card ≤ k)
    (hg : LocalOn S g) : DependsOnAtMost k g :=
  ⟨Unit, inferInstance, fun _ => S, fun _ => g, fun _ => ⟨hS, hg⟩, fun H => by simp⟩

theorem const (k : ℕ) (c : ℂ) : DependsOnAtMost k (fun _ : α → β => c) :=
  of_localOn (S := ∅) (by simp) fun _ _ _ => rfl

theorem zero (k : ℕ) : DependsOnAtMost k (0 : (α → β) → ℂ) := const k 0

theorem mono {k l : ℕ} {F : (α → β) → ℂ} (hF : DependsOnAtMost k F) (hkl : k ≤ l) :
    DependsOnAtMost l F := by
  obtain ⟨ι, _, S, g, hg, hF⟩ := hF
  exact ⟨ι, inferInstance, S, g, fun i => ⟨(hg i).1.trans hkl, (hg i).2⟩, hF⟩

theorem add {k : ℕ} {F G : (α → β) → ℂ} (hF : DependsOnAtMost k F)
    (hG : DependsOnAtMost k G) : DependsOnAtMost k (F + G) := by
  obtain ⟨ι, _, S, g, hg, hF⟩ := hF
  obtain ⟨κ, _, T, h, hh, hG⟩ := hG
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim S T, Sum.elim g h, ?_, fun H => ?_⟩
  · rintro (i | i)
    · exact hg i
    · exact hh i
  · simp [Fintype.sum_sum_type, hF, hG]

theorem sum {k : ℕ} {κ : Type} (s : Finset κ) (F : κ → (α → β) → ℂ)
    (hF : ∀ j ∈ s, DependsOnAtMost k (F j)) : DependsOnAtMost k (∑ j ∈ s, F j) :=
  Finset.sum_induction _ (DependsOnAtMost k) (fun _ _ => add) (zero k) hF

/-- The pointwise finite sum, stated on values. -/
theorem sum_apply {k : ℕ} {κ : Type} (s : Finset κ) (F : κ → (α → β) → ℂ)
    (hF : ∀ j ∈ s, DependsOnAtMost k (F j)) :
    DependsOnAtMost k (fun H => ∑ j ∈ s, F j H) := by
  convert sum s F hF using 1
  funext H
  rw [Finset.sum_apply]

theorem mul {k l r : ℕ} {F G : (α → β) → ℂ} (hF : DependsOnAtMost k F)
    (hG : DependsOnAtMost l G) (hr : k + l ≤ r) : DependsOnAtMost r (fun H => F H * G H) := by
  classical
  obtain ⟨ι, _, S, g, hg, hF⟩ := hF
  obtain ⟨κ, _, T, h, hh, hG⟩ := hG
  refine ⟨ι × κ, inferInstance, fun p => S p.1 ∪ T p.2, fun p H => g p.1 H * h p.2 H,
    fun p => ⟨?_, ?_⟩, fun H => ?_⟩
  · exact (Finset.card_union_le _ _).trans ((Nat.add_le_add (hg p.1).1 (hh p.2).1).trans hr)
  · intro H H' hHH'
    show g p.1 H * h p.2 H = g p.1 H' * h p.2 H'
    rw [(hg p.1).2 H H' fun x hx => hHH' x (Finset.mem_union_left _ hx),
      (hh p.2).2 H H' fun x hx => hHH' x (Finset.mem_union_right _ hx)]
  · show F H * G H = ∑ p : ι × κ, g p.1 H * h p.2 H
    rw [hF, hG, Finset.sum_mul_sum, Fintype.sum_prod_type]

theorem star {k : ℕ} {F : (α → β) → ℂ} (hF : DependsOnAtMost k F) :
    DependsOnAtMost k (fun H => Star.star (F H)) := by
  obtain ⟨ι, _, S, g, hg, hF⟩ := hF
  refine ⟨ι, inferInstance, S, fun i H => Star.star (g i H),
    fun i => ⟨(hg i).1, fun H H' hHH' => by beta_reduce; rw [(hg i).2 H H' hHH']⟩, fun H => ?_⟩
  beta_reduce
  rw [hF, star_sum]

end DependsOnAtMost

end Depends

/-! ## Matrices whose entries depend on few points -/

section Entries

variable {α β : Type} {d : ℕ}

/-- Every entry of the matrix-valued function `M` depends on at most `k` points
    of the table. -/
def EntriesDependOnAtMost (k : ℕ) (M : (α → β) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ i j, DependsOnAtMost k (fun H => M H i j)

namespace EntriesDependOnAtMost

theorem const (k : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    EntriesDependOnAtMost k (fun _ : α → β => M) :=
  fun _ _ => DependsOnAtMost.const k _

theorem mul {k l r : ℕ} {M N : (α → β) → Matrix (Fin d) (Fin d) ℂ}
    (hM : EntriesDependOnAtMost k M) (hN : EntriesDependOnAtMost l N) (hr : k + l ≤ r) :
    EntriesDependOnAtMost r (fun H => M H * N H) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact DependsOnAtMost.sum_apply Finset.univ (fun a H => M H i a * N H a j)
    fun a _ => (hM i a).mul (hN a j) hr

theorem conjTranspose {k : ℕ} {M : (α → β) → Matrix (Fin d) (Fin d) ℂ}
    (hM : EntriesDependOnAtMost k M) : EntriesDependOnAtMost k (fun H => (M H)ᴴ) := by
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact (hM j i).star

theorem trace {k : ℕ} {M : (α → β) → Matrix (Fin d) (Fin d) ℂ}
    (hM : EntriesDependOnAtMost k M) : DependsOnAtMost k (fun H => (M H).trace) := by
  simp only [Matrix.trace, Matrix.diag]
  exact DependsOnAtMost.sum_apply Finset.univ (fun i H => M H i i) fun i _ => hM i i

end EntriesDependOnAtMost

/-- A chain `U_q O U_{q-1} ⋯ O U_0` with `q` copies of an oracle matrix whose
    entries each depend on at most one point has entries depending on at most
    `q` points. -/
theorem chainOp_entries_dependsOn (O : (α → β) → Matrix (Fin d) (Fin d) ℂ)
    (hO : EntriesDependOnAtMost 1 O) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      EntriesDependOnAtMost q (fun H => chainOp (O H) q U)
  | 0, U => EntriesDependOnAtMost.const 0 (U 0 : Matrix (Fin d) (Fin d) ℂ)
  | q + 1, U =>
    ((chainOp_entries_dependsOn O hO q (Fin.tail U)).mul hO le_rfl).mul
      (EntriesDependOnAtMost.const 0 (U 0 : Matrix (Fin d) (Fin d) ℂ)) (by omega)

end Entries

/-! ## The acceptance probability depends on at most `2q` points -/

section Adv

variable {m n w q : ℕ} [NeZero n]

/-- Every entry of the oracle unitary reads the table at one point: the entry
    `(a, b)` is determined by `H` at the query-register value of `b`. -/
theorem oracleU_entries_dependsOn (m n w : ℕ) [NeZero n] :
    EntriesDependOnAtMost 1
      (fun H : Fin m → Fin n => (oracleU m n w H : Matrix (Fin (m * n * w)) _ ℂ)) := by
  intro a b
  obtain ⟨⟨⟨x, y⟩, z⟩, rfl⟩ := (oracleIndex m n w).surjective b
  refine DependsOnAtMost.of_localOn (S := {x}) (by simp) fun H H' hH => ?_
  have hx : H x = H' x := hH x (Finset.mem_singleton_self x)
  simp only [oracleU_eq_permUnitary, permUnitary_apply, oraclePerm_apply, hx]

/-- The acceptance probability of the standard run, as the complex trace
    `tr (X ρ Xᴴ)` with `X = final * runOp A H`. -/
def prOutC (A : QAdv m n w q) (H : Fin m → Fin n) : ℂ :=
  ((A.final * runOp A H) * A.init.val * (A.final * runOp A H)ᴴ).trace

theorem prOut_eq_ofReal_re (A : QAdv m n w q) (H : Fin m → Fin n) :
    prOut A H = ENNReal.ofReal (prOutC A H).re := by
  unfold prOut prTrue_Q prOutC
  rw [run_branch_true]

theorem prOutC_re_nonneg (A : QAdv m n w q) (H : Fin m → Fin n) : 0 ≤ (prOutC A H).re := by
  have h := trace_re_nonneg_of_psd ((run A H).branch_psd true A.init.val A.init.psd)
  rwa [run_branch_true] at h

/-- The acceptance probability of a `q`-query adversary depends on at most `2q`
    points of the table. -/
theorem prOutC_dependsOn (A : QAdv m n w q) :
    DependsOnAtMost (2 * q) (fun H => prOutC A H) := by
  have hR : EntriesDependOnAtMost q (fun H : Fin m → Fin n => runOp A H) :=
    chainOp_entries_dependsOn _ (oracleU_entries_dependsOn m n w) q A.U
  have hX : EntriesDependOnAtMost q (fun H : Fin m → Fin n => A.final * runOp A H) :=
    (EntriesDependOnAtMost.const 0 A.final).mul hR (by omega)
  exact ((hX.mul (EntriesDependOnAtMost.const 0 A.init.val) (r := q) (by omega)).mul
    hX.conjTranspose (by omega)).trace

end Adv

/-! ## Weights that agree on small cylinders -/

section Cylinder

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The tables that agree with `H₀` on `S`. -/
def cyl (S : Finset α) (H₀ : α → β) : Finset (α → β) :=
  Finset.univ.filter fun H => ∀ x ∈ S, H x = H₀ x

/-- `μ` and `ν` give equal mass to every set of tables fixed on at most `k`
    points. -/
def CylinderAgree (k : ℕ) (μ ν : (α → β) → ℂ) : Prop :=
  ∀ S : Finset α, S.card ≤ k → ∀ H₀ : α → β, ∑ H ∈ cyl S H₀, μ H = ∑ H ∈ cyl S H₀, ν H

/-- `μ` is `k`-wise independent: its mass on every set of tables fixed on at
    most `k` points equals the uniform mass. -/
def KWiseIndep (k : ℕ) (μ : (α → β) → ℝ≥0) : Prop :=
  ∀ S : Finset α, S.card ≤ k → ∀ H₀ : α → β,
    ∑ H ∈ cyl S H₀, μ H = ∑ _H ∈ cyl S H₀, ((Fintype.card (α → β) : ℝ≥0))⁻¹

/-- Weights with equal mass on every `S`-cylinder give equal averages to a
    function local on `S`. -/
theorem sum_mul_eq_of_localOn {S : Finset α} {g : (α → β) → ℂ} (hg : LocalOn S g)
    {μ ν : (α → β) → ℂ} (h : ∀ H₀, ∑ H ∈ cyl S H₀, μ H = ∑ H ∈ cyl S H₀, ν H) :
    ∑ H, μ H * g H = ∑ H, ν H * g H := by
  let r : (α → β) → (S → β) := fun H x => H x
  rw [← Finset.sum_fiberwise Finset.univ r (fun H => μ H * g H),
    ← Finset.sum_fiberwise Finset.univ r (fun H => ν H * g H)]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hne : ∃ H₀, r H₀ = t
  · obtain ⟨H₀, rfl⟩ := hne
    have hfib : (Finset.univ.filter fun H => r H = r H₀) = cyl S H₀ := by
      ext H
      simp [cyl, r, funext_iff]
    have hgc : ∀ H ∈ cyl S H₀, g H = g H₀ := fun H hH =>
      hg H H₀ (Finset.mem_filter.mp hH).2
    rw [hfib, Finset.sum_congr rfl fun H hH => congrArg (μ H * ·) (hgc H hH),
      Finset.sum_congr rfl fun H hH => congrArg (ν H * ·) (hgc H hH),
      ← Finset.sum_mul, ← Finset.sum_mul, h H₀]
  · have hemp : (Finset.univ.filter fun H => r H = t) = ∅ := by
      ext H
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h' => hne ⟨H, h'⟩
    rw [hemp, Finset.sum_empty, Finset.sum_empty]

/-- Weights that agree on every cylinder of at most `k` points give equal
    averages to every function depending on at most `k` points. -/
theorem sum_mul_eq_of_cylinderAgree {k : ℕ} {μ ν : (α → β) → ℂ} (hμν : CylinderAgree k μ ν)
    {F : (α → β) → ℂ} (hF : DependsOnAtMost k F) :
    ∑ H, μ H * F H = ∑ H, ν H * F H := by
  obtain ⟨ι, _, S, g, hg, hF⟩ := hF
  simp only [hF, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => sum_mul_eq_of_localOn (hg i).2 (hμν (S i) (hg i).1)

end Cylinder

/-! ## Averages of the acceptance probability -/

section Avg

variable {m n w q : ℕ} [NeZero n]

/-- A non-negative average of the acceptance probability is the real part of
    the complex average of `prOutC`. -/
theorem sum_mul_prOut_eq (A : QAdv m n w q) (μ : (Fin m → Fin n) → ℝ≥0) :
    ∑ H, (μ H : ℝ≥0∞) * prOut A H =
      ENNReal.ofReal (∑ H, ((μ H : ℝ) : ℂ) * prOutC A H).re := by
  rw [Complex.re_sum, ENNReal.ofReal_sum_of_nonneg fun H _ => by
    rw [Complex.re_ofReal_mul]; exact mul_nonneg (μ H).2 (prOutC_re_nonneg A H)]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [Complex.re_ofReal_mul, ENNReal.ofReal_mul (μ H).coe_nonneg, ENNReal.ofReal_coe_nnreal,
    prOut_eq_ofReal_re]

/-- Two weights on tables that agree on every cylinder of at most `2q` points
    give the same average acceptance probability to a `q`-query adversary. -/
theorem prOut_avg_eq_of_cylinderAgree (A : QAdv m n w q) (μ ν : (Fin m → Fin n) → ℝ≥0)
    (h : CylinderAgree (2 * q) (fun H => ((μ H : ℝ) : ℂ)) (fun H => ((ν H : ℝ) : ℂ))) :
    ∑ H, (μ H : ℝ≥0∞) * prOut A H = ∑ H, (ν H : ℝ≥0∞) * prOut A H := by
  rw [sum_mul_prOut_eq, sum_mul_prOut_eq, sum_mul_eq_of_cylinderAgree h (prOutC_dependsOn A)]

/-- Zhandry, CRYPTO 2012, Theorem 6.1: under a `2q`-wise independent weight on
    tables, the average acceptance probability of a `q`-query adversary equals
    its average under the uniform weight. -/
theorem prOut_avg_eq_of_kWise (A : QAdv m n w q) (μ : (Fin m → Fin n) → ℝ≥0)
    (hμ : KWiseIndep (2 * q) μ) :
    ∑ H, (μ H : ℝ≥0∞) * prOut A H =
      ∑ H, ((Fintype.card (Fin m → Fin n) : ℝ≥0) : ℝ≥0∞)⁻¹ * prOut A H := by
  have hc : ((Fintype.card (Fin m → Fin n) : ℝ≥0) : ℝ≥0∞)⁻¹ =
      (((Fintype.card (Fin m → Fin n) : ℝ≥0))⁻¹ : ℝ≥0) :=
    (ENNReal.coe_inv (by simp [NeZero.ne n])).symm
  rw [hc]
  refine prOut_avg_eq_of_cylinderAgree A μ _ fun S hS H₀ => ?_
  have h2 := congrArg (fun r : ℝ≥0 => ((r : ℝ) : ℂ)) (hμ S hS H₀)
  simpa only [NNReal.coe_sum, Complex.ofReal_sum] using h2

end Avg

end CatCrypt.Quantum.QROM
