/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SDist
import CatCryptCore.Prob.Support

/-!
# State-independent lift `SDistr → SPComp`

The canonical stateless embedding of a distribution `SDistr α` into the stateful
probabilistic computation monad `SPComp α`, obtained by threading the heap
through unchanged. This is pure CatCrypt program-logic content — it mentions no
external probability library — so it lives in the minimal core basis, where both
`SDistr` and `SPComp` are defined.

The `UCMonadMorphism` packaging (`sdistrLift`) and the VCVio interoperability
built on top of this lift live downstream (`CatCrypt.Crypto.UCMonad.SDistrLift`
and the `catcrypt-vcvio` package), which is why those consumers can depend on a
VCVio-free core module rather than dragging the VCVio library into their closure.

## Main definitions

* `sdistrToSPComp` — the state-independent lift.

## Main results

* `sdistrToSPComp_pure` / `sdistrToSPComp_bind` — monad-morphism laws.
* `sdistrToSPComp_isPure` — the lift produces heap-independent computations.
* `bind_sdistrToSPComp_eq` — running a bind of the lift at a heap.
* `marginalize_heap` — marginalising the heap out of an `SDistr (Bool × Heap)`.
-/

namespace CatCrypt.Crypto.SDistrLift

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

/-- Lift `SDistr` to `SPComp` by ignoring the heap. -/
noncomputable def sdistrToSPComp {α : Type} (d : SDistr α) : SPComp α :=
  fun h => SDistr.bind d (fun a => SDistr.pure (a, h))

@[simp] theorem sdistrToSPComp_run {α : Type} (d : SDistr α) (h : Heap) :
    sdistrToSPComp d h = SDistr.bind d (fun a => SDistr.pure (a, h)) := rfl

/-- The state-independent lift preserves pure. -/
theorem sdistrToSPComp_pure {α : Type} (a : α) :
    sdistrToSPComp (SDistr.pure a) = SPComp.pure a := by
  funext h; simp [sdistrToSPComp, SDistr.pure_bind, SPComp.pure]

/-- The state-independent lift preserves bind. -/
theorem sdistrToSPComp_bind {α β : Type} (d : SDistr α) (f : α → SDistr β) :
    sdistrToSPComp (SDistr.bind d f) =
    SPComp.bind (sdistrToSPComp d) (fun a => sdistrToSPComp (f a)) := by
  funext h
  unfold sdistrToSPComp SPComp.bind
  simp only [SDistr.bind_assoc, SDistr.pure_bind]

/-- The state-independent lift produces `IsPure` computations. -/
theorem sdistrToSPComp_isPure {α : Type} (d : SDistr α) :
    SPComp.IsPure (sdistrToSPComp d) :=
  ⟨d, fun _ => rfl⟩

/-- Running a bind of the state-independent lift against a distinguisher at a
    fixed heap collapses to the underlying `SDistr` bind. -/
theorem bind_sdistrToSPComp_eq {β : Type} (d : SDistr β) (D : β → SPComp Bool)
    (h₀ : Heap) :
    SPComp.bind (sdistrToSPComp d) D h₀ = SDistr.bind d (fun b => D b h₀) := by
  unfold sdistrToSPComp SPComp.bind
  simp only [SDistr.bind_assoc, SDistr.pure_bind]

/-- Marginalising the heap out of an `SDistr (Bool × Heap)`: summing the
    probability of `(true, ·)` over all heaps equals the probability of `true`
    under the first-projection push-forward. -/
theorem marginalize_heap (M : SDistr (Bool × Heap)) :
    (∑' (h : Heap), (M : PMF _) (some (true, h))) =
    (SDistr.bind M (fun p => SDistr.pure p.1) : SDistr Bool) (some true) := by
  simp only [SDistr.bind, SDistr.pure, SDistr.fail]
  rw [PMF.bind_apply]; symm
  rw [tsum_option_split]
  simp only [PMF.pure_apply, Option.some.injEq, reduceCtorEq, ite_false, mul_zero, zero_add]
  rw [tsum_bool_prod_eq]
  simp

end CatCrypt.Crypto.SDistrLift
