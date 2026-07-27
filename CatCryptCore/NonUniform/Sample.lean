/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Code
import CatCryptCore.Unary.Lossless

/-!
# Sampling from an arbitrary sub-distribution

`SPComp.sample` samples uniformly from a finite nonempty type. `sampleFrom d`
samples from an arbitrary `SDistr`, leaving the heap unchanged, so that
non-uniform distributions — centered binomial, rejection-sampling output,
biased coins, discrete Gaussians — are expressible as `SPComp` programs.

## Main definitions

* `sampleFrom d` — sample from `d : SDistr α`, heap unchanged
* `ofPMF p` — the total distribution `p : PMF α` viewed as an `SDistr α`

## Main results

* `sampleFrom_uniform` — `sampleFrom (SDistr.uniform α) = SPComp.sample α`, so
  uniform sampling is a definitional special case
* `sampleFrom_eq_liftSDistr` — `sampleFrom` and the existing `liftSDistr` agree
* `sampleFrom_bind_apply` — `(sampleFrom d >>= k) h = d.bind fun a => k a h`
* `mass_sampleFrom`, `isLossless_sampleFrom_iff` — mass of the computation is the
  mass of the distribution
* `bind_const_of_mass_one`, `dead_sampleFrom` — a lossless sample whose result is
  discarded is a no-op
-/

namespace CatCrypt.NonUniform

open CatCrypt.Core CatCrypt.Prob CatCrypt.Unary
open scoped ENNReal

variable {α β γ : Type*}

/-! ## The combinator -/

/-- Sample from an arbitrary sub-distribution, leaving the heap unchanged.
    The computation fails with probability `d none`. -/
noncomputable def sampleFrom (d : SDistr α) : SPComp α :=
  fun h => d.bind fun a => SDistr.pure (a, h)

@[simp]
theorem sampleFrom_apply (d : SDistr α) (h : Heap) :
    sampleFrom d h = d.bind fun a => SDistr.pure (a, h) := rfl

/-- Uniform sampling is the `sampleFrom` at the uniform distribution. -/
theorem sampleFrom_uniform (α : Type*) [Fintype α] [Nonempty α] :
    sampleFrom (SDistr.uniform α) = SPComp.sample α := rfl

/-- `sampleFrom` agrees with the `SDistr → SPComp` lift already in `Core.Code`. -/
theorem sampleFrom_eq_liftSDistr {α : Type} (d : SDistr α) :
    sampleFrom d = liftSDistr d := rfl

/-! ## Monadic laws -/

/-- Bind interaction: the sampled value is fed to the continuation at the
    unchanged heap, so the whole computation is a bind at the `SDistr` level. -/
theorem sampleFrom_bind_apply (d : SDistr α) (k : α → SPComp β) (h : Heap) :
    (SPComp.bind (sampleFrom d) k) h = d.bind fun a => k a h := by
  simp only [SPComp.bind, sampleFrom_apply, SDistr.bind_assoc, SDistr.pure_bind]

/-- Operator form of `sampleFrom_bind_apply`. -/
theorem sampleFrom_hBind_apply {α β : Type} (d : SDistr α) (k : α → SPComp β) (h : Heap) :
    (sampleFrom d >>= k) h = d.bind fun a => k a h :=
  sampleFrom_bind_apply d k h

/-- Sampling from a point mass is returning. -/
@[simp]
theorem sampleFrom_pure (a : α) : sampleFrom (SDistr.pure a) = SPComp.pure a :=
  funext fun h => SDistr.pure_bind a fun a => SDistr.pure (a, h)

/-- Sampling from the everywhere-failing distribution is failure. -/
@[simp]
theorem sampleFrom_fail : sampleFrom (SDistr.fail : SDistr α) = SPComp.fail :=
  funext fun h => SDistr.bind_fail fun a => SDistr.pure (a, h)

/-- Two successive samples are one sample from the bound distribution. -/
theorem sampleFrom_bind_sampleFrom (d : SDistr α) (f : α → SDistr β) :
    SPComp.bind (sampleFrom d) (fun a => sampleFrom (f a)) = sampleFrom (d.bind f) := by
  funext h
  simp only [sampleFrom_bind_apply, sampleFrom_apply, SDistr.bind_assoc]

/-- `sampleFrom d` does not read or write the heap. -/
theorem sampleFrom_isPure (d : SDistr α) : SPComp.IsPure (sampleFrom d) :=
  ⟨d, fun _ => rfl⟩

/-! ## Mass and losslessness -/

/-- The failure probability of `sampleFrom d` is the failure probability of `d`. -/
theorem sampleFrom_apply_none (d : SDistr α) (h : Heap) :
    (sampleFrom d h) none = d none := by
  simp only [sampleFrom_apply, SDistr.bind, PMF.bind_apply, SDistr.tsum_option_eq_add,
    SDistr.fail_apply_none, mul_one, SDistr.pure_apply_none, mul_zero, tsum_zero, add_zero]

/-- The mass of `sampleFrom d` is the mass of `d`. -/
theorem mass_sampleFrom (d : SDistr α) (h : Heap) :
    SDistr.mass (sampleFrom d h) = SDistr.mass d := by
  simp only [SDistr.mass, sampleFrom_apply_none]

/-- `sampleFrom d` is lossless exactly when `d` is a total distribution. -/
theorem isLossless_sampleFrom_iff (d : SDistr α) :
    isLossless (sampleFrom d) ↔ SDistr.mass d = 1 :=
  ⟨fun hl => (mass_sampleFrom d Heap.empty).symm.trans (hl Heap.empty),
   fun hm h => (mass_sampleFrom d h).trans hm⟩

/-- A total distribution gives a lossless computation. -/
theorem isLossless_sampleFrom (d : SDistr α) (hd : SDistr.mass d = 1) :
    isLossless (sampleFrom d) :=
  (isLossless_sampleFrom_iff d).mpr hd

/-! ## Discarding a lossless sample -/

/-- Binding a total distribution to a constant continuation is that constant.
    Generalizes `SDistr.uniform_bind_const` from uniform to arbitrary mass-one
    distributions. -/
theorem bind_const_of_mass_one {d : SDistr α} (hd : SDistr.mass d = 1)
    (e : SDistr β) : d.bind (fun _ => e) = e := by
  have hnone : d none = 0 :=
    Classical.byContradiction fun hne =>
      absurd hd (ne_of_lt (ENNReal.sub_lt_self (by norm_num) (by norm_num) hne))
  have hsum : ∑' a : α, d (some a) = 1 := by
    simpa only [SDistr.tsum_option_eq_add, hnone, zero_add] using PMF.tsum_coe d
  refine SDistr.eq_of_some_eq fun b => ?_
  simp only [SDistr.bind, PMF.bind_apply, SDistr.tsum_option_eq_add, SDistr.fail_apply_some,
    mul_zero, zero_add, ENNReal.tsum_mul_right, hsum, one_mul]

/-- A lossless sample whose result is unused can be dropped.
    Generalizes `dead_sample` from uniform to arbitrary mass-one distributions. -/
theorem dead_sampleFrom {d : SDistr α} (hd : SDistr.mass d = 1) (k : SPComp β) :
    SPComp.bind (sampleFrom d) (fun _ => k) = k :=
  funext fun h =>
    (sampleFrom_bind_apply d _ h).trans (bind_const_of_mass_one hd (k h))

/-! ## Total distributions from `PMF` -/

/-- A `PMF` viewed as a never-failing `SDistr`. -/
noncomputable def ofPMF (p : PMF α) : SDistr α := p.map some

@[simp]
theorem ofPMF_apply_some (p : PMF α) (a : α) : ofPMF p (some a) = p a := by
  classical
  simp only [ofPMF, PMF.map_apply, Option.some.injEq]
  rw [tsum_eq_single a fun a' ha' => if_neg (Ne.symm ha'), if_pos rfl]

@[simp]
theorem ofPMF_apply_none (p : PMF α) : ofPMF p none = 0 := by
  simp only [ofPMF, PMF.map_apply, reduceCtorEq, if_false, tsum_zero]

@[simp]
theorem mass_ofPMF (p : PMF α) : SDistr.mass (ofPMF p) = 1 := by
  simp only [SDistr.mass, ofPMF_apply_none, tsub_zero]

/-- `SDistr.uniform` is `ofPMF` of the uniform `PMF`. -/
theorem ofPMF_uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] :
    ofPMF (PMF.uniformOfFintype α) = SDistr.uniform α := rfl

/-- `sampleFrom (ofPMF p)` is lossless. -/
theorem isLossless_sampleFrom_ofPMF (p : PMF α) : isLossless (sampleFrom (ofPMF p)) :=
  isLossless_sampleFrom _ (mass_ofPMF p)

end CatCrypt.NonUniform
