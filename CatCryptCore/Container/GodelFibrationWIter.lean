/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.GodelFibrationW
public import Mathlib.Data.Matrix.Mul

/-!
# Iteration of derivations and the use counts of a retry loop

A cut substitutes a derivation of `φ` for the hypothesis `φ` at position `0` of a derivation
(`WDeriv.cut`, `Deriv.cut`, the composite `→`-introduction then `→`-elimination). Bounded
recursion iterates a step derivation `step m` of `φ (m + 1)` from the invariant `φ m` and the
context, `m` times from a base derivation of `φ 0` (`WDeriv.iterD`, `Deriv.iterD`); `WDeriv.iter`
and `Deriv.iter` are the instances at a constant invariant.

When each step uses the invariant `a` times and hypothesis `j` of the context `b` times, the use
count of hypothesis `j` after `m` iterations is the first entry of the `m`-th power of the affine
count matrix `[[a, b], [0, 1]]` (`affMat`, the matrix of `clockMat` in `Container/DNGraded.lean`
over a commutative semiring) applied to the vector `(c, 1)` of the base count `c`
(`WDeriv.wuseCount_iterD_eq_mulVec`), with closed form `a ^ m * c + b * ∑_{i < m} a ^ i`. A step
that uses the invariant once gives `c + m * b`: `m` iterations of a step using a hypothesis `b`
times use it `m * b` times.

The retry instance: a realized axiom `f` from an attempt hypothesis to a success atom `s` whose
expected demand has total weight at most `p⁻¹` (a retry loop with success probability `p`), and
a step that adds one success to the invariant `q m` ("`m` successes collected"). After `m`
iterations the attempt hypothesis is used `m * p⁻¹` times in expectation beyond the base
(`WDeriv.wuseCount_retryCollect`), and the expected demand of the realizer on it is at most that
count (`WDeriv.mass_back_retryCollect_le`). This is the bound `k * (C / p)` of the threshold
extractor `collectN` (`Container/ExpectedDNOp.lean`, `ecost_collectN_le`) at trial cost `C = 1`.

## Main definitions

* `affMat`, `affVec` — affine count matrices and the vectors they act on;
* `DNLogic.WDeriv.cut`, `DNLogic.WDeriv.iterD`, `DNLogic.WDeriv.iter`,
  `DNLogic.WDeriv.retryStep`, `DNLogic.WDeriv.retryCollect`;
* `DNLogic.Deriv.cut`, `DNLogic.Deriv.iterD`, `DNLogic.Deriv.iter`.

## Main results

* `affMat_mul`, `affMat_pow`, `affMat_mulVec_affVec` — the composition law of affine counts;
* `DNLogic.WDeriv.wuseCount_iterD`, `DNLogic.WDeriv.wuseCount_iterD_eq_mulVec`,
  `DNLogic.WDeriv.wuseCount_iterD_of_one`, `DNLogic.WDeriv.mass_back_iterD_le` — use counts and
  weighted soundness of iteration;
* `DNLogic.WDeriv.wuseCount_retryCollect`, `DNLogic.WDeriv.wuseCount_retryCollect_of_zero`,
  `DNLogic.WDeriv.mass_back_retryCollect_le` — `m` successes cost `m * p⁻¹` expected attempts;
* `DNLogic.Deriv.useCount_iterD`, `DNLogic.Deriv.useCount_iterD_eq_mulVec`,
  `DNLogic.Deriv.useCount_iterD_of_one`, `DNLogic.Deriv.card_back_iterD_le`.

## References

* M. Bellare, O. Goldreich, *On Defining Proofs of Knowledge*, CRYPTO 1992, §6.
* B. L. Kaminski, J.-P. Katoen, C. Matheja, F. Olmedo, *Weakest precondition reasoning for
  expected runtimes of randomized algorithms*, J. ACM 65(5) (2018).

Search words: iteration rule, bounded recursion, cut, use count, count matrix, matrix power,
retry loop, rewinding, threshold extractor, expected use count, weighted derivation.
-/

set_option autoImplicit false

@[expose] public section

open scoped NNReal ENNReal

universe u

namespace CatCrypt.Container

/-! ## Affine count matrices -/

section AffMat

variable {R : Type*} [CommSemiring R]

/-- The affine count matrix `[[a, b], [0, 1]]`, rows and columns ordered data token (`false`),
constant (`true`): `a` uses of the input and `b` further uses. -/
def affMat (a b : R) : Matrix Bool Bool R :=
  Matrix.of fun y x => bif y then (bif x then 1 else 0) else (bif x then b else a)

/-- The vector `(c, 1)` of a count `c`. -/
def affVec (c : R) : Bool → R := fun x => bif x then 1 else c

/-- **Affine counts compose by the matrix product**: uses multiply, and the further uses are
`b₂ + a₂ * b₁`. -/
theorem affMat_mul (a₂ b₂ a₁ b₁ : R) :
    affMat a₂ b₂ * affMat a₁ b₁ = affMat (a₂ * a₁) (b₂ + a₂ * b₁) := by
  ext y x
  cases y <;> cases x <;> simp [affMat, Matrix.mul_apply, add_comm]

/-- The matrix of one use and no further uses is the identity. -/
theorem affMat_one_zero : affMat (1 : R) 0 = 1 := by
  ext y x
  cases y <;> cases x <;> simp [affMat]

/-- The `m`-th power of an affine count matrix. -/
theorem affMat_pow (a b : R) (m : ℕ) :
    affMat a b ^ m = affMat (a ^ m) (b * ∑ i ∈ Finset.range m, a ^ i) := by
  induction m with
  | zero => simp [affMat_one_zero]
  | succ m ih =>
    rw [pow_succ', ih, affMat_mul, Finset.sum_range_succ']
    simp only [pow_succ', ← Finset.mul_sum, pow_zero]
    congr 1
    ring

/-- An affine count matrix sends the vector of a count `c` to the vector of `a * c + b`. -/
theorem affMat_mulVec_affVec (a b c : R) :
    (affMat a b).mulVec (affVec c) = affVec (a * c + b) := by
  ext x
  cases x <;> simp [affMat, affVec, Matrix.mulVec, dotProduct, add_comm]

end AffMat

namespace DNLogic

variable {I : Type u} {n : ℕ}

/-! ## Iteration of weighted derivations -/

namespace WDeriv

/-- The cut: a derivation of `φ` substituted for the hypothesis `φ` at position `0`. -/
def cut {Γ : Fin n → Form I} {φ ψ : Form I} (s : WDeriv (consF φ Γ) ψ) (e : WDeriv Γ φ) :
    WDeriv Γ ψ :=
  impE (impI s) e

/-- Unfolding equation of `wuseCount` at a cut: the uses of the context, and the uses of the
cut hypothesis times the uses in the substituted derivation. -/
theorem wuseCount_cut {Γ : Fin n → Form I} {φ ψ : Form I} (s : WDeriv (consF φ Γ) ψ)
    (e : WDeriv Γ φ) (j : Fin n) :
    (cut s e).wuseCount j = s.wuseCount j.succ + s.wuseCount 0 * e.wuseCount j := rfl

/-- **Bounded recursion.** From a base derivation of `φ 0` and steps deriving `φ (m + 1)` from the
invariant `φ m` at position `0`, a derivation of `φ m` for every `m`. -/
def iterD {Γ : Fin n → Form I} (φ : ℕ → Form I) (step : ∀ m, WDeriv (consF (φ m) Γ) (φ (m + 1)))
    (base : WDeriv Γ (φ 0)) : ∀ m, WDeriv Γ (φ m)
  | 0 => base
  | m + 1 => cut (step m) (iterD φ step base m)

/-- Iteration at a constant invariant: `m` applications of a step deriving `φ` from `φ`. -/
def iter {Γ : Fin n → Form I} {φ : Form I} (step : WDeriv (consF φ Γ) φ) (base : WDeriv Γ φ)
    (m : ℕ) : WDeriv Γ φ :=
  iterD (fun _ => φ) (fun _ => step) base m

variable {Γ : Fin n → Form I} {φ : ℕ → Form I} {step : ∀ m, WDeriv (consF (φ m) Γ) (φ (m + 1))}
  {base : WDeriv Γ (φ 0)}

/-- **Use counts of iteration, closed form.** Steps that use the invariant `a` times and
hypothesis `j` `b` times give `a ^ m * c + b * ∑_{i < m} a ^ i` uses of `j` after `m` iterations
from a base with `c` uses. -/
theorem wuseCount_iterD (j : Fin n) (a b : ℝ≥0∞) (ha : ∀ m, (step m).wuseCount 0 = a)
    (hb : ∀ m, (step m).wuseCount j.succ = b) (m : ℕ) :
    (iterD φ step base m).wuseCount j =
      a ^ m * base.wuseCount j + b * ∑ i ∈ Finset.range m, a ^ i := by
  induction m with
  | zero => simp [iterD]
  | succ m ih =>
    rw [iterD, wuseCount_cut, ha, hb, ih, Finset.sum_range_succ']
    simp only [pow_succ', ← Finset.mul_sum, pow_zero]
    ring

/-- **Use counts of iteration as a matrix power.** The use vector `(count, 1)` of hypothesis `j`
after `m` iterations is the `m`-th power of the step's affine count matrix applied to the use
vector of the base. -/
theorem wuseCount_iterD_eq_mulVec (j : Fin n) (a b : ℝ≥0∞) (ha : ∀ m, (step m).wuseCount 0 = a)
    (hb : ∀ m, (step m).wuseCount j.succ = b) (m : ℕ) :
    affVec ((iterD φ step base m).wuseCount j) =
      (affMat a b ^ m).mulVec (affVec (base.wuseCount j)) := by
  rw [affMat_pow, affMat_mulVec_affVec, wuseCount_iterD j a b ha hb]

/-- **Iteration multiplies use counts.** Steps that use the invariant once and hypothesis `j`
`b` times give `c + m * b` uses of `j` after `m` iterations from a base with `c` uses. -/
theorem wuseCount_iterD_of_one (j : Fin n) (b : ℝ≥0∞) (ha : ∀ m, (step m).wuseCount 0 = 1)
    (hb : ∀ m, (step m).wuseCount j.succ = b) (m : ℕ) :
    (iterD φ step base m).wuseCount j = base.wuseCount j + m * b := by
  rw [wuseCount_iterD j 1 b ha hb]
  simp [mul_comm]

/-- **Weighted soundness of iteration.** The realizer of `m` iterations of steps that use the
invariant once and hypothesis `j` `b` times demands `j` at most `c + m * b` times in
expectation. -/
theorem mass_back_iterD_le (j : Fin n) (b : ℝ≥0∞) (ha : ∀ m, (step m).wuseCount 0 = 1)
    (hb : ∀ m, (step m).wuseCount j.succ = b) (m : ℕ) (i : I) (w : (wctx Γ).W i)
    (c : (φ m).wdn.C i ((iterD φ step base m).realize.fwd i w)) :
    (WMeasure.mass ((iterD φ step base m).realize.back i w c) (fun x => x.1 = j) : ℝ≥0∞) ≤
      base.wuseCount j + m * b :=
  ((iterD φ step base m).mass_back_le j i w c).trans
    (le_of_eq (wuseCount_iterD_of_one j b ha hb m))

/-! ## The retry loop -/

/-- One round of the threshold extractor: from the invariant `q m` at position `0` and the
attempt hypothesis `k`, the realized axiom `f` of a retry loop finds a success `s` with expected
demand of total weight at most `p⁻¹` on the attempts, and `h` adds it to the invariant. -/
noncomputable def retryStep {Γ : Fin n → Form I} (k : Fin n) {q : ℕ → I → Prop} {s : I → Prop}
    (f : (Γ k).wdn.WHom (Form.atom s).wdn) (p : ℝ≥0)
    (hf : ∀ i w c, WMeasure.total (f.back i w c) ≤ p⁻¹)
    (h : ∀ m i, q m i → s i → q (m + 1) i) (m : ℕ) :
    WDeriv (consF (Form.atom (q m)) Γ) (Form.atom (q (m + 1))) :=
  atom₂ (h m) (hyp (Γ := consF (Form.atom (q m)) Γ) 0)
    (hom f p⁻¹ hf (hyp (Γ := consF (Form.atom (q m)) Γ) k.succ))

/-- The threshold extractor as a derivation: `m` rounds of `retryStep` from a base derivation of
`q 0`. -/
noncomputable def retryCollect {Γ : Fin n → Form I} (k : Fin n) {q : ℕ → I → Prop}
    {s : I → Prop} (f : (Γ k).wdn.WHom (Form.atom s).wdn) (p : ℝ≥0)
    (hf : ∀ i w c, WMeasure.total (f.back i w c) ≤ p⁻¹)
    (h : ∀ m i, q m i → s i → q (m + 1) i) (base : WDeriv Γ (Form.atom (q 0))) (m : ℕ) :
    WDeriv Γ (Form.atom (q m)) :=
  iterD (fun m => Form.atom (q m)) (retryStep k f p hf h) base m

/-- **Expected attempts of the threshold extractor.** `m` successes, each from a retry loop with
expected demand `p⁻¹` per success, use the attempt hypothesis `c + m * p⁻¹` times from a base
with `c` uses. -/
theorem wuseCount_retryCollect (k : Fin n) {q : ℕ → I → Prop} {s : I → Prop}
    (f : (Γ k).wdn.WHom (Form.atom s).wdn) (p : ℝ≥0)
    (hf : ∀ i w c, WMeasure.total (f.back i w c) ≤ p⁻¹)
    (h : ∀ m i, q m i → s i → q (m + 1) i) (base : WDeriv Γ (Form.atom (q 0))) (m : ℕ) :
    (retryCollect k f p hf h base m).wuseCount k = base.wuseCount k + m * (p⁻¹ : ℝ≥0) := by
  refine wuseCount_iterD_of_one k _ (fun m => ?_) (fun m => ?_) m
  · simp [retryStep, wuseCount, wuses, (Fin.succ_ne_zero k).symm]
  · simp [retryStep, wuseCount, wuses, Fin.succ_ne_zero]

/-- **`m` successes cost `m / p` expected attempts.** From a base that makes no attempt, the
threshold extractor uses the attempt hypothesis `m * p⁻¹` times in expectation. -/
theorem wuseCount_retryCollect_of_zero (k : Fin n) {q : ℕ → I → Prop} {s : I → Prop}
    (f : (Γ k).wdn.WHom (Form.atom s).wdn) {p : ℝ≥0} (hp : p ≠ 0)
    (hf : ∀ i w c, WMeasure.total (f.back i w c) ≤ p⁻¹)
    (h : ∀ m i, q m i → s i → q (m + 1) i) (base : WDeriv Γ (Form.atom (q 0)))
    (h0 : base.wuseCount k = 0) (m : ℕ) :
    (retryCollect k f p hf h base m).wuseCount k = m * (p : ℝ≥0∞)⁻¹ := by
  rw [wuseCount_retryCollect, h0, zero_add, ENNReal.coe_inv hp]

/-- **Weighted soundness of the threshold extractor.** The realizer of `m` rounds demands the
attempt hypothesis at most `c + m * p⁻¹` times in expectation. -/
theorem mass_back_retryCollect_le (k : Fin n) {q : ℕ → I → Prop} {s : I → Prop}
    (f : (Γ k).wdn.WHom (Form.atom s).wdn) (p : ℝ≥0)
    (hf : ∀ i w c, WMeasure.total (f.back i w c) ≤ p⁻¹)
    (h : ∀ m i, q m i → s i → q (m + 1) i) (base : WDeriv Γ (Form.atom (q 0))) (m : ℕ) (i : I)
    (w : (wctx Γ).W i)
    (c : (Form.atom (q m)).wdn.C i ((retryCollect k f p hf h base m).realize.fwd i w)) :
    (WMeasure.mass ((retryCollect k f p hf h base m).realize.back i w c) (fun x => x.1 = k) :
        ℝ≥0∞) ≤ base.wuseCount k + m * (p⁻¹ : ℝ≥0) :=
  ((retryCollect k f p hf h base m).mass_back_le k i w c).trans
    (le_of_eq (wuseCount_retryCollect k f p hf h base m))

end WDeriv

/-! ## Iteration of unweighted derivations -/

namespace Deriv

/-- The cut: a derivation of `φ` substituted for the hypothesis `φ` at position `0`. -/
def cut {Γ : Fin n → Form I} {φ ψ : Form I} (s : Deriv (consF φ Γ) ψ) (e : Deriv Γ φ) :
    Deriv Γ ψ :=
  impE (impI s) e

/-- Unfolding equation of `useCount` at a cut. -/
theorem useCount_cut {Γ : Fin n → Form I} {φ ψ : Form I} (s : Deriv (consF φ Γ) ψ)
    (e : Deriv Γ φ) (j : Fin n) :
    (cut s e).useCount j = s.useCount j.succ + s.useCount 0 * e.useCount j := rfl

/-- **Bounded recursion.** From a base derivation of `φ 0` and steps deriving `φ (m + 1)` from the
invariant `φ m` at position `0`, a derivation of `φ m` for every `m`. -/
def iterD {Γ : Fin n → Form I} (φ : ℕ → Form I) (step : ∀ m, Deriv (consF (φ m) Γ) (φ (m + 1)))
    (base : Deriv Γ (φ 0)) : ∀ m, Deriv Γ (φ m)
  | 0 => base
  | m + 1 => cut (step m) (iterD φ step base m)

/-- Iteration at a constant invariant: `m` applications of a step deriving `φ` from `φ`. -/
def iter {Γ : Fin n → Form I} {φ : Form I} (step : Deriv (consF φ Γ) φ) (base : Deriv Γ φ)
    (m : ℕ) : Deriv Γ φ :=
  iterD (fun _ => φ) (fun _ => step) base m

variable {Γ : Fin n → Form I} {φ : ℕ → Form I} {step : ∀ m, Deriv (consF (φ m) Γ) (φ (m + 1))}
  {base : Deriv Γ (φ 0)}

/-- **Use counts of iteration, closed form.** Steps that use the invariant `a` times and
hypothesis `j` `b` times give `a ^ m * c + b * ∑_{i < m} a ^ i` uses of `j` after `m` iterations
from a base with `c` uses. -/
theorem useCount_iterD (j : Fin n) (a b : ℕ∞) (ha : ∀ m, (step m).useCount 0 = a)
    (hb : ∀ m, (step m).useCount j.succ = b) (m : ℕ) :
    (iterD φ step base m).useCount j =
      a ^ m * base.useCount j + b * ∑ i ∈ Finset.range m, a ^ i := by
  induction m with
  | zero => simp [iterD]
  | succ m ih =>
    rw [iterD, useCount_cut, ha, hb, ih, Finset.sum_range_succ']
    simp only [pow_succ', ← Finset.mul_sum, pow_zero]
    ring

/-- **Use counts of iteration as a matrix power.** -/
theorem useCount_iterD_eq_mulVec (j : Fin n) (a b : ℕ∞) (ha : ∀ m, (step m).useCount 0 = a)
    (hb : ∀ m, (step m).useCount j.succ = b) (m : ℕ) :
    affVec ((iterD φ step base m).useCount j) =
      (affMat a b ^ m).mulVec (affVec (base.useCount j)) := by
  rw [affMat_pow, affMat_mulVec_affVec, useCount_iterD j a b ha hb]

/-- **Iteration multiplies use counts.** Steps that use the invariant once and hypothesis `j`
`b` times give `c + m * b` uses of `j` after `m` iterations from a base with `c` uses. -/
theorem useCount_iterD_of_one (j : Fin n) (b : ℕ∞) (ha : ∀ m, (step m).useCount 0 = 1)
    (hb : ∀ m, (step m).useCount j.succ = b) (m : ℕ) :
    (iterD φ step base m).useCount j = base.useCount j + m * b := by
  rw [useCount_iterD j 1 b ha hb]
  simp [mul_comm]

/-- **Quantitative soundness of iteration.** The realizer of `m` iterations of steps that use the
invariant once and hypothesis `j` `b` times demands at most `c + m * b` counter-witnesses of
`j`. -/
theorem card_back_iterD_le (j : Fin n) (b : ℕ∞) (ha : ∀ m, (step m).useCount 0 = 1)
    (hb : ∀ m, (step m).useCount j.succ = b) (m : ℕ) (i : I) (w : (ctx Γ).W i)
    (c : (φ m).dn.C i ((iterD φ step base m).realize.fwd i w)) :
    ((((iterD φ step base m).realize.back i w c).countP fun x => x.1 = j : ℕ) : ℕ∞) ≤
      base.useCount j + m * b :=
  ((iterD φ step base m).card_back_le j i w c).trans
    (le_of_eq (useCount_iterD_of_one j b ha hb m))

end Deriv

end DNLogic

end CatCrypt.Container
