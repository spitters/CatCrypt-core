/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.NonUniform.WhileApprox
import CatCryptCore.Unary.Rules
import CatCryptCore.Unary.Event

/-!
# The unary invariant rule for bounded loop approximants

A predicate `I` on heaps that the body preserves whenever the guard holds is an
invariant of every approximant `whileApprox guard body n`: from a heap satisfying
`I`, each outcome of the approximant satisfies `I` and falsifies the guard.

The rule needs no termination hypothesis. A run that exhausts its budget fails,
and failure carries no value mass, so the postcondition holds vacuously on it;
the judgment is partial correctness. Termination enters separately, through
losslessness: at a budget where the approximant has mass one, the postcondition
has probability one.

## Main results

* `pHoare_whileApprox` — the invariant rule at every budget
* `pHoare_whileApprox_conseq` — the same with the postcondition weakened
* `prEvent_whileApprox_eq_one` — probability one under conditional losslessness
* `prEvent_whileApprox_eq_one_of_isLossless` — the unconditional variant
-/

set_option autoImplicit false

namespace CatCrypt.NonUniform

open CatCrypt.Core CatCrypt.Prob CatCrypt.Unary
open scoped ENNReal

variable {guard : Heap → Bool} {body : SPComp Unit} {I : Heap → Prop}

/-! ## Base case -/

/-- The zero-budget approximant is `SPComp.fail`, which satisfies every judgment:
its support contains no outcome. -/
theorem pHoare_whileApprox_zero (P : UPre) (Q : UPost Unit)
    (guard : Heap → Bool) (body : SPComp Unit) :
    pHoare P (whileApprox guard body 0) Q :=
  pHoare_fail

/-! ## The invariant rule -/

/-- Invariant rule for the bounded approximants. If `body` restores `I` from any
heap satisfying `I` on which the guard holds, then from a heap satisfying `I` the
approximant `whileApprox guard body n` ends in a heap satisfying `I` on which the
guard is false, for every budget `n`. -/
theorem pHoare_whileApprox
    (hbody : pHoare (fun h => I h ∧ guard h = true) body (fun _ h' => I h')) (n : ℕ) :
    pHoare I (whileApprox guard body n) (fun _ h' => I h' ∧ guard h' = false) := by
  induction n with
  | zero => exact pHoare_whileApprox_zero _ _ guard body
  | succ n ih =>
    intro h₀ hI a h' hsupp
    by_cases hg : guard h₀ = true
    · rw [whileApprox_succ_of_guard hg] at hsupp
      exact pHoare_bind hbody (fun _ => ih) h₀ ⟨hI, hg⟩ a h' hsupp
    · have hgf : guard h₀ = false := Bool.not_eq_true _ ▸ hg
      rw [whileApprox_succ_of_not_guard hgf] at hsupp
      exact pHoare_ret (a := ()) (P := fun h => I h ∧ guard h = false)
        (Q := fun _ h' => I h' ∧ guard h' = false)
        (fun _ hP => hP) h₀ ⟨hI, hgf⟩ a h' hsupp

/-- The invariant rule with the postcondition weakened: any `Q` implied by the
invariant together with the guard being false. -/
theorem pHoare_whileApprox_conseq {Q : UPost Unit}
    (hbody : pHoare (fun h => I h ∧ guard h = true) body (fun _ h' => I h'))
    (hQ : ∀ h, I h → guard h = false → Q () h) (n : ℕ) :
    pHoare I (whileApprox guard body n) Q :=
  pHoare_mono_post (pHoare_whileApprox hbody n)
    (fun a h ⟨hI, hg⟩ => match a with | () => hQ h hI hg)

/-! ## Termination-gated probability -/

/-- At a budget where the approximant is lossless on heaps satisfying the
invariant, the invariant together with the guard being false has probability one. -/
theorem prEvent_whileApprox_eq_one
    (hbody : pHoare (fun h => I h ∧ guard h = true) body (fun _ h' => I h'))
    {n : ℕ} (hll : isLosslessIf I (whileApprox guard body n))
    (h₀ : Heap) (hI : I h₀) :
    prEvent (whileApprox guard body n h₀) (fun _ h' => I h' ∧ guard h' = false) = 1 :=
  (prEvent_of_pHoare (P := I) (pHoare_whileApprox hbody n) h₀ hI).trans (hll h₀ hI)

/-- `prEvent_whileApprox_eq_one` under unconditional losslessness of the
approximant. -/
theorem prEvent_whileApprox_eq_one_of_isLossless
    (hbody : pHoare (fun h => I h ∧ guard h = true) body (fun _ h' => I h'))
    {n : ℕ} (hll : isLossless (whileApprox guard body n))
    (h₀ : Heap) (hI : I h₀) :
    prEvent (whileApprox guard body n h₀) (fun _ h' => I h' ∧ guard h' = false) = 1 :=
  prEvent_whileApprox_eq_one hbody (isLossless_implies_if I hll) h₀ hI

/-- The weakened form at probability one: a postcondition implied by the
invariant and the guard being false holds with probability one at a budget where
the approximant is lossless. -/
theorem prEvent_whileApprox_conseq_eq_one {Q : UPost Unit}
    (hbody : pHoare (fun h => I h ∧ guard h = true) body (fun _ h' => I h'))
    (hQ : ∀ h, I h → guard h = false → Q () h)
    {n : ℕ} (hll : isLosslessIf I (whileApprox guard body n))
    (h₀ : Heap) (hI : I h₀) :
    prEvent (whileApprox guard body n h₀) (fun a h' => Q a h') = 1 :=
  (prEvent_of_pHoare (P := I) (pHoare_whileApprox_conseq hbody hQ n) h₀ hI).trans (hll h₀ hI)

end CatCrypt.NonUniform
