/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.NonUniform.WhileApproxMono
import CatCryptCore.NonUniform.WhileUnary
import CatCryptCore.NonUniform.Limit

/-!
# The unbounded loop

`whileLoop guard body` runs `body` while `guard` holds of the current heap, with
no bound on the number of iterations. It is the limit of `whileApprox`: the mass
it assigns to a heap is the probability of reaching that heap and leaving the loop
after any finite number of iterations, and the failure mass is the probability of
running forever.

The pHL rule transports from the approximants because `pHoare` constrains the
support: a heap in the support of the limit is in the support of some
approximant, and the invariant rule holds at every budget.
-/

set_option autoImplicit false

namespace CatCrypt.NonUniform

open CatCrypt.Core CatCrypt.Prob CatCrypt.Unary

/-- `while guard do body`, as the limit of its bounded approximants. -/
noncomputable def whileLoop (guard : Heap → Bool) (body : SPComp Unit) :
    SPComp Unit :=
  fun h => mlim (fun n => whileApprox guard body n h)
    (whileApprox_apply_mono guard body h)

@[simp] theorem whileLoop_apply_some (guard : Heap → Bool) (body : SPComp Unit)
    (h : Heap) (p : Unit × Heap) :
    whileLoop guard body h (some p)
      = ⨆ n, whileApprox guard body n h (some p) := rfl

/-- An outcome of the loop is an outcome of some approximant: a supremum over the
budgets is nonzero only if one of them is. -/
theorem exists_whileApprox_ne_zero {guard : Heap → Bool} {body : SPComp Unit}
    {h : Heap} {p : Unit × Heap} (hp : whileLoop guard body h (some p) ≠ 0) :
    ∃ n, whileApprox guard body n h (some p) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  exact hp (by simpa [whileLoop_apply_some] using iSup_eq_bot.mpr hcon)

/-- **The pHL rule for the unbounded loop.** If the body preserves the invariant
while the guard holds, then every outcome of the loop satisfies the invariant with
the guard false.

This is partial correctness: the mass on which the loop runs forever is failure
mass, which carries no outcome and so satisfies the postcondition vacuously. -/
theorem pHoare_whileLoop {guard : Heap → Bool} {body : SPComp Unit}
    {I : Heap → Prop}
    (hbody : pHoare (fun h => I h ∧ guard h = true) body (fun _ h' => I h')) :
    pHoare I (whileLoop guard body) (fun _ h' => I h' ∧ guard h' = false) := by
  intro h hI a h' hne
  obtain ⟨n, hn⟩ := exists_whileApprox_ne_zero hne
  exact pHoare_whileApprox hbody n h hI a h' hn

/-- The consequence form of the loop rule. -/
theorem pHoare_whileLoop_conseq {guard : Heap → Bool} {body : SPComp Unit}
    {I : Heap → Prop} {Q : UPost Unit}
    (hbody : pHoare (fun h => I h ∧ guard h = true) body (fun _ h' => I h'))
    (hQ : ∀ h, I h → guard h = false → Q () h) :
    pHoare I (whileLoop guard body) Q := by
  intro h hI a h' hne
  obtain ⟨hinv, hg⟩ := pHoare_whileLoop hbody h hI a h' hne
  cases a
  exact hQ h' hinv hg

end CatCrypt.NonUniform
