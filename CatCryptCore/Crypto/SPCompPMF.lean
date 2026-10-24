/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.NomPkgBridge

/-!
# Probability mass functions as heap-independent computations

A probability mass function `p : PMF α` defines the computation `liftPMF p : SPComp α`
that returns a sample of `p` and leaves the heap unchanged. Conversely, a Boolean
computation family `Dist : α → SPComp Bool` defines the distribution `outBool Dist a` of
its output bit when run from the empty heap.

## Main definitions

* `liftPMF` — a probability mass function as a computation that leaves the heap unchanged
* `outBool` — the output bit of a Boolean computation run from the empty heap

## Main results

* `liftPMF_bind_liftPMF`, `liftPMF_pure`, `liftPMF_bind_pure`, `sample_eq_liftPMF` —
  `liftPMF` commutes with bind and pure, and uniform sampling is its lift
* `liftPMF_isPure`, `liftPMF_noFail` — `liftPMF p` does not read or write the heap and
  never fails
* `prTrue_liftPMF`, `prTrue_liftPMF_toOuterMeasure` — `liftPMF p` outputs `true` with
  probability `p true`; `prTrue_sample_bind_liftPMF` — the same after a uniform sample
* `outBool_apply_true`, `prTrue_liftPMF_bind` — the output bit of a distinguisher, and a
  distinguisher run on a sample of `p`
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

namespace CatCrypt.Crypto

/-! ## Lifting a probability mass function -/

/-- A probability mass function as a computation that leaves the heap unchanged. -/
noncomputable def liftPMF {α : Type} (p : PMF α) : SPComp α :=
  fun h => p.map fun a => some (a, h)

theorem sdistr_bind_map_some {α β γ : Type} (p : PMF α) (g : α → β) (F : β → SDistr γ) :
    SDistr.bind (p.map fun a => some (g a)) F = p.bind fun a => F (g a) := by
  unfold SDistr.bind
  rw [PMF.bind_map]
  rfl

theorem liftPMF_bind_apply {α β : Type} (p : PMF α) (f : α → SPComp β) (h : Heap) :
    SPComp.bind (liftPMF p) f h = p.bind fun a => f a h := by
  unfold SPComp.bind liftPMF
  exact sdistr_bind_map_some p (fun a => (a, h)) _

/-- A lifted distribution followed by lifted continuations is the lift of the bind. -/
theorem liftPMF_bind_liftPMF {α β : Type} (p : PMF α) (f : α → PMF β) :
    SPComp.bind (liftPMF p) (fun a => liftPMF (f a)) = liftPMF (p.bind f) := by
  funext h
  rw [liftPMF_bind_apply]
  unfold liftPMF
  rw [PMF.map_bind]

/-- `SPComp.pure` is the lift of a point mass. -/
theorem liftPMF_pure {α : Type} (a : α) :
    (SPComp.pure a : SPComp α) = liftPMF (PMF.pure a) := by
  funext h
  simp [liftPMF, SPComp.pure, SDistr.pure, PMF.pure_map]

/-- A lifted distribution followed by a pure continuation is the lift of the image. -/
theorem liftPMF_bind_pure {α β : Type} (p : PMF α) (f : α → β) :
    SPComp.bind (liftPMF p) (fun a => SPComp.pure (f a)) = liftPMF (p.map f) := by
  simp only [liftPMF_pure, liftPMF_bind_liftPMF]
  rfl

/-- Uniform sampling is the lift of the uniform distribution. -/
theorem sample_eq_liftPMF (α : Type) [Fintype α] [Nonempty α] :
    SPComp.sample α = liftPMF (PMF.uniformFintype α) := by
  funext h
  unfold SPComp.sample SDistr.uniform liftPMF
  rw [sdistr_bind_map_some]
  unfold SDistr.pure
  rw [← PMF.bind_pure_comp]
  rfl

/-- A probability mass function lifted to a computation is heap-independent. -/
theorem liftPMF_isPure {α : Type} (p : PMF α) : SPComp.IsPure (liftPMF p) := by
  refine ⟨p.map some, fun h => ?_⟩
  simp only [liftPMF, SDistr.bind, SDistr.pure, PMF.bind_map]
  rw [← PMF.bind_pure_comp]
  rfl

/-- A probability mass function lifted to a computation never fails. -/
theorem liftPMF_noFail {α : Type} (p : PMF α) : SPComp.NoFail (liftPMF p) := fun _ => by
  simp [liftPMF, PMF.map_apply]

/-- A lifted distribution on `Bool` outputs `true` with probability `p true`. -/
theorem prTrue_liftPMF (p : PMF Bool) (h₀ : Heap) : prTrue (liftPMF p) h₀ = p true := by
  unfold prTrue liftPMF
  simp only [PMF.map_apply]
  rw [ENNReal.tsum_comm]
  rw [tsum_eq_single true (fun b hb => by
    refine ENNReal.tsum_eq_zero.mpr fun h => ?_
    simp [Ne.symm hb])]
  rw [tsum_eq_single h₀ (fun h hh => by simp [hh])]
  simp

/-- A lifted distribution on `Bool` outputs `true` with the probability of the event
`{b | b = true}`. -/
theorem prTrue_liftPMF_toOuterMeasure (p : PMF Bool) (h₀ : Heap) :
    prTrue (liftPMF p) h₀ = p.toOuterMeasure {b | b = true} := by
  rw [prTrue_liftPMF, show {b : Bool | b = true} = {true} from Set.ext fun _ => Iff.rfl,
    PMF.toOuterMeasure_apply_singleton]

/-- A uniform sample followed by lifted distributions outputs `true` with the probability
of `true` under the bind of the uniform distribution. -/
theorem prTrue_sample_bind_liftPMF {α : Type} [Fintype α] [Nonempty α]
    (f : α → PMF Bool) (h₀ : Heap) :
    prTrue (SPComp.bind (SPComp.sample α) fun a => liftPMF (f a)) h₀ =
      ((PMF.uniformFintype α).bind f) true := by
  rw [sample_eq_liftPMF, liftPMF_bind_liftPMF, prTrue_liftPMF]

/-! ## The output bit of a distinguisher -/

/-- The output bit of `Dist a` run from the empty heap, `false` on failure. -/
noncomputable def outBool {α : Type} (Dist : α → SPComp Bool) (a : α) : PMF Bool :=
  (Dist a Heap.empty).map fun r => match r with | some (b, _) => b | none => false

theorem outBool_apply_true {α : Type} (Dist : α → SPComp Bool) (a : α) :
    outBool Dist a true = prTrue (Dist a) Heap.empty := by
  unfold outBool prTrue
  rw [PMF.map_apply]
  have hsupp : Function.support (fun r : Option (Bool × Heap) =>
      if true = (match r with | some (b, _) => b | none => false) then (Dist a Heap.empty) r
      else 0) ⊆ Set.range (fun h : Heap => some (true, h)) := by
    intro r hr
    rcases r with _ | ⟨b, h⟩
    · simp_all
    · cases b
      · simp_all
      · simp_all
  symm
  convert (Function.Injective.tsum_eq (fun h₁ h₂ e => by simpa using e) hsupp) using 1
  · simp
  · simp_all

/-- A lifted distribution followed by a distinguisher, from the empty heap, outputs `true`
with the probability that the output bit of the distinguisher on a sample is `true`. -/
theorem prTrue_liftPMF_bind {α : Type} (p : PMF α) (Dist : α → SPComp Bool) :
    prTrue ((liftPMF p).bind Dist) Heap.empty = (p.bind (outBool Dist)) true := by
  rw [prTrue_bind_eq_weighted, PMF.bind_apply]
  simp only [liftPMF, PMF.map_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (some (a, Heap.empty)) fun o ho => by simp [ho]]
  simp [outBool_apply_true]

end CatCrypt.Crypto
