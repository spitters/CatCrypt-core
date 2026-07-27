/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.NonUniform.Conditional

/-!
# Monotone limits of sub-distributions

A sequence `f : ℕ → SDistr α` is a `MonoSeq` when the weight it assigns to each
value is non-decreasing in `n`. Its limit `mlim f h` assigns to each value the
supremum of the weights, and puts the residual mass on failure.

`SDistr α` is a probability mass function on `Option α`, of total mass exactly
one, so the failure component of the limit is determined: it is `1` minus the
total weight of the values, and constructing the limit needs the bound
`∑' a, ⨆ n, f n (some a) ≤ 1`.

## Main definitions

* `MonoSeq f` — the weight of every value is non-decreasing along `f`
* `mlim f h` — the limit of a `MonoSeq`

## Main results

* `tsum_iSup_of_monotone` — summation commutes with a monotone supremum
* `mlim_bind` — the limit commutes with `bind` on the left
* `bind_mlim` — the limit commutes with `bind` on the right
* `mass_mlim` — the mass of the limit is the supremum of the masses
* `mlim_const` — a constant sequence is its own limit

## Correspondence with EasyCrypt

`mlim_bind` and `bind_mlim` are the images of `dlet_lim` and `dlim_let` of the
`Distr` theory, the two laws that carry the denotation of `while` through a bind.
-/

set_option autoImplicit false

namespace CatCrypt.NonUniform

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

variable {α β : Type*}

/-! ## Summation against a monotone supremum -/

/-- Summation commutes with the supremum of a family that is monotone in the
supremum index. -/
theorem tsum_iSup_of_monotone {g : α → ℕ → ℝ≥0∞} (hg : ∀ a, Monotone (g a)) :
    ∑' a, ⨆ n, g a n = ⨆ n, ∑' a, g a n := by
  rw [ENNReal.tsum_eq_iSup_sum]
  simp only [ENNReal.finsetSum_iSup_of_monotone hg]
  rw [iSup_comm]
  exact iSup_congr fun _ => ENNReal.tsum_eq_iSup_sum.symm

/-! ## The weight a bind assigns to a value -/

/-- The weight of a value under a bind is the average of its weights under the
continuation. The failure branch contributes nothing. -/
theorem bind_apply_some (d : SDistr α) (g : α → SDistr β) (b : β) :
    (d.bind g) (some b) = ∑' a, d (some a) * g a (some b) := by
  rw [SDistr.bind, PMF.bind_apply, SDistr.tsum_option_eq_add]
  simp only [SDistr.fail_apply_some, mul_zero, zero_add]

/-! ## Non-decreasing sequences -/

/-- A sequence of sub-distributions whose weight at every value is non-decreasing. -/
def MonoSeq (f : ℕ → SDistr α) : Prop :=
  ∀ n m, n ≤ m → ∀ a, f n (some a) ≤ f m (some a)

/-- The weight of a fixed value along a `MonoSeq` is a monotone function of the
index. -/
theorem MonoSeq.monotone {f : ℕ → SDistr α} (h : MonoSeq f) (a : α) :
    Monotone fun n => f n (some a) := fun _ _ hnm => h _ _ hnm a

/-- A constant sequence is non-decreasing. -/
theorem monoSeq_const (d : SDistr α) : MonoSeq (fun _ => d) := fun _ _ _ _ => le_rfl

/-- Binding a non-decreasing sequence on the left keeps it non-decreasing. -/
theorem MonoSeq.bind_left {f : ℕ → SDistr α} (h : MonoSeq f) (g : α → SDistr β) :
    MonoSeq fun n => (f n).bind g := by
  intro n m hnm b
  simp only [bind_apply_some]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul' (h n m hnm a) le_rfl

/-- Binding a pointwise non-decreasing family on the right gives a non-decreasing
sequence. -/
theorem monoSeq_bind_right (d : SDistr α) {f : ℕ → α → SDistr β}
    (h : ∀ a, MonoSeq fun n => f n a) :
    MonoSeq fun n => d.bind fun a => f n a := by
  intro n m hnm b
  simp only [bind_apply_some]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (h a n m hnm b)

/-! ## The limit -/

/-- The total weight of the values in the limit of a non-decreasing sequence is at
most one. -/
theorem tsum_iSup_le_one (f : ℕ → SDistr α) (h : MonoSeq f) :
    ∑' a, ⨆ n, f n (some a) ≤ 1 := by
  rw [tsum_iSup_of_monotone h.monotone]
  exact iSup_le fun n => (mass_eq_tsum (f n)).symm.trans_le (mass_le_one (f n))

/-- The limit of a non-decreasing sequence of sub-distributions: each value gets
the supremum of its weights, and failure gets the rest. -/
noncomputable def mlim (f : ℕ → SDistr α) (h : MonoSeq f) : SDistr α :=
  ⟨fun oa =>
      match oa with
      | none => 1 - ∑' a, ⨆ n, f n (some a)
      | some a => ⨆ n, f n (some a),
   ENNReal.summable.hasSum_iff.mpr (by
     rw [SDistr.tsum_option_eq_add]
     exact tsub_add_cancel_of_le (tsum_iSup_le_one f h))⟩

/-- The limit assigns to a value the supremum of the weights of the sequence. -/
@[simp]
theorem mlim_apply_some (f : ℕ → SDistr α) (h : MonoSeq f) (a : α) :
    mlim f h (some a) = ⨆ n, f n (some a) := rfl

/-- The failure weight of the limit is the mass the values leave over. -/
theorem mlim_apply_none (f : ℕ → SDistr α) (h : MonoSeq f) :
    mlim f h none = 1 - ∑' a, ⨆ n, f n (some a) := rfl

/-- Every member of the sequence is below the limit at every value. -/
theorem apply_some_le_mlim (f : ℕ → SDistr α) (h : MonoSeq f) (n : ℕ) (a : α) :
    f n (some a) ≤ mlim f h (some a) := le_iSup (fun k => f k (some a)) n

/-- The mass of the limit is the supremum of the masses. -/
theorem mass_mlim (f : ℕ → SDistr α) (h : MonoSeq f) :
    SDistr.mass (mlim f h) = ⨆ n, SDistr.mass (f n) := by
  rw [SDistr.mass, mlim_apply_none,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top (tsum_iSup_le_one f h),
    tsum_iSup_of_monotone h.monotone]
  exact iSup_congr fun n => (mass_eq_tsum (f n)).symm

/-- A constant sequence has itself as limit. -/
theorem mlim_const (d : SDistr α) : mlim (fun _ => d) (monoSeq_const d) = d :=
  SDistr.eq_of_some_eq fun _ => iSup_const

/-! ## Interchange with bind -/

/-- The limit commutes with `bind` on the left: binding the limit of a
non-decreasing sequence is the limit of the binds. -/
theorem mlim_bind (f : ℕ → SDistr α) (h : MonoSeq f) (g : α → SDistr β) :
    (mlim f h).bind g = mlim (fun n => (f n).bind g) (h.bind_left g) := by
  refine SDistr.eq_of_some_eq fun b => ?_
  rw [bind_apply_some, mlim_apply_some]
  have hstep : ∀ a : α,
      (mlim f h) (some a) * g a (some b) = ⨆ n, f n (some a) * g a (some b) := fun a => by
    rw [mlim_apply_some, ENNReal.iSup_mul]
  rw [tsum_congr hstep,
    tsum_iSup_of_monotone (g := fun a n => f n (some a) * g a (some b))
      fun a _ _ hnm => mul_le_mul' (h _ _ hnm a) le_rfl]
  exact iSup_congr fun n => (bind_apply_some (f n) g b).symm

/-- The limit commutes with `bind` on the right: binding into the limit of a
pointwise non-decreasing family is the limit of the binds. -/
theorem bind_mlim (d : SDistr α) (f : ℕ → α → SDistr β)
    (h : ∀ a, MonoSeq fun n => f n a) :
    (d.bind fun a => mlim (fun n => f n a) (h a))
      = mlim (fun n => d.bind fun a => f n a) (monoSeq_bind_right d h) := by
  refine SDistr.eq_of_some_eq fun b => ?_
  rw [bind_apply_some, mlim_apply_some]
  have hstep : ∀ a : α,
      d (some a) * mlim (fun n => f n a) (h a) (some b)
        = ⨆ n, d (some a) * f n a (some b) := fun a => by
    rw [mlim_apply_some, ENNReal.mul_iSup]
  rw [tsum_congr hstep,
    tsum_iSup_of_monotone (g := fun a n => d (some a) * f n a (some b))
      fun a _ _ hnm => mul_le_mul' le_rfl (h a _ _ hnm b)]
  exact iSup_congr fun n => (bind_apply_some d (fun a => f n a) b).symm

end CatCrypt.NonUniform
