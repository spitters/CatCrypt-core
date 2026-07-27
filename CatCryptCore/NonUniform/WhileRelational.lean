/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.NonUniform.WhileApprox
import CatCryptCore.Relational.Rules

/-!
# pRHL rules for bounded loop approximants

`rHoare Φ c₁ c₂ Ψ` holds when the output sub-distributions of `c₁` and `c₂`,
run from any `Φ`-related pair of heaps, admit a coupling supported in `Ψ`. This
file gives the rules relating `whileApprox guard₁ body₁ n` to
`whileApprox guard₂ body₂ n` at a fixed budget `n`.

A relational invariant `I` that forces the two guards to agree, together with
bodies that preserve `I` while the guards hold, relates the two approximants at
every budget. The two sides run in lockstep: the same `n` on both sides. A
`Coupling` matches its two marginals exactly, so the failure mass carried by a
joint sub-distribution is shared by both sides; at equal budgets the two
approximants do lose the same mass, which is what makes the lockstep statement
couplable.

## Main results

* `rHoare_fail_fail` — a coupling of two failed computations, on any pre- and
  postcondition
* `rHoare_whileApprox_zero` — the budget-`0` case, where both approximants are
  `SPComp.fail`
* `rHoare_whileApprox_step` — one synchronous iteration at budget `n + 1`, given
  the judgment for the bodies and the judgment at budget `n`
* `rHoare_whileApprox` — the synchronous invariant rule at every budget
* `rHoare_whileApprox_same` — the specialization to one guard and one body
-/

set_option autoImplicit false

namespace CatCrypt.NonUniform

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational

variable {α β : Type*}

/-! ## Failure against failure -/

/-- Two failed computations are related by any postcondition: the zero
sub-distribution is a coupling of `SPComp.fail` with itself, and its support is
empty. -/
theorem rHoare_fail_fail {Φ : RPre} {Ψ : RPost α β} :
    rHoare Φ (SPComp.fail : SPComp α) (SPComp.fail : SPComp β) Ψ :=
  fun _ _ _ => liftR_fail

/-- The rule above and the library's `rHoare_fail` are the same proposition. -/
example : @Relational.rHoare_fail = @rHoare_fail_fail := rfl

/-! ## The approximants at a fixed budget -/

/-- At budget `0` both approximants are `SPComp.fail`, so any pre- and
postcondition relate them. -/
theorem rHoare_whileApprox_zero (guard₁ guard₂ : Heap → Bool)
    (body₁ body₂ : SPComp Unit) (Φ : RPre) (Ψ : RPost Unit Unit) :
    rHoare Φ (whileApprox guard₁ body₁ 0) (whileApprox guard₂ body₂ 0) Ψ :=
  rHoare_fail_fail

/-- One synchronous iteration. From a pair of heaps satisfying `I` with both
guards true, a judgment for the two bodies and a judgment for the two
approximants at budget `n` give the judgment at budget `n + 1`. -/
theorem rHoare_whileApprox_step {guard₁ guard₂ : Heap → Bool}
    {body₁ body₂ : SPComp Unit} {I : RPre} {Ψ : RPost Unit Unit} {n : ℕ}
    (hbody : rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard₁ h₁ = true ∧ guard₂ h₂ = true)
      body₁ body₂ (fun _ h₁ _ h₂ => I h₁ h₂))
    (hrec : rHoare I (whileApprox guard₁ body₁ n) (whileApprox guard₂ body₂ n) Ψ) :
    rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard₁ h₁ = true ∧ guard₂ h₂ = true)
      (whileApprox guard₁ body₁ (n + 1)) (whileApprox guard₂ body₂ (n + 1)) Ψ := by
  intro h₁ h₂ hpre
  rw [whileApprox_succ_of_guard hpre.2.1, whileApprox_succ_of_guard hpre.2.2]
  exact rHoare_bind hbody (fun _ _ => hrec) h₁ h₂ hpre

/--
The synchronous invariant rule for the bounded approximants.

If the relational invariant `I` forces the two guards to agree, and the two
bodies preserve `I` from any `I`-related pair of heaps at which the guards hold,
then at every budget `n` the two approximants are related by `I` together with
both guards being false.
-/
theorem rHoare_whileApprox {guard₁ guard₂ : Heap → Bool}
    {body₁ body₂ : SPComp Unit} {I : RPre}
    (hguard : ∀ h₁ h₂, I h₁ h₂ → guard₁ h₁ = guard₂ h₂)
    (hbody : rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard₁ h₁ = true ∧ guard₂ h₂ = true)
      body₁ body₂ (fun _ h₁ _ h₂ => I h₁ h₂))
    (n : ℕ) :
    rHoare I (whileApprox guard₁ body₁ n) (whileApprox guard₂ body₂ n)
      (fun _ h₁ _ h₂ => I h₁ h₂ ∧ guard₁ h₁ = false ∧ guard₂ h₂ = false) := by
  induction n with
  | zero => exact rHoare_whileApprox_zero _ _ _ _ _ _
  | succ n ih =>
    intro h₁ h₂ hI
    have hg : guard₁ h₁ = guard₂ h₂ := hguard h₁ h₂ hI
    cases hg₁ : guard₁ h₁ with
    | true =>
      have hg₂ : guard₂ h₂ = true := hg ▸ hg₁
      exact rHoare_whileApprox_step hbody ih h₁ h₂ ⟨hI, hg₁, hg₂⟩
    | false =>
      have hg₂ : guard₂ h₂ = false := hg ▸ hg₁
      rw [whileApprox_succ_of_not_guard hg₁, whileApprox_succ_of_not_guard hg₂]
      exact liftR_pure ⟨hI, hg₁, hg₂⟩

/-- The synchronous rule with one guard and one body on both sides: the
invariant only has to make the guard agree on the two heaps. -/
theorem rHoare_whileApprox_same {guard : Heap → Bool} {body : SPComp Unit} {I : RPre}
    (hguard : ∀ h₁ h₂, I h₁ h₂ → guard h₁ = guard h₂)
    (hbody : rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard h₁ = true ∧ guard h₂ = true)
      body body (fun _ h₁ _ h₂ => I h₁ h₂))
    (n : ℕ) :
    rHoare I (whileApprox guard body n) (whileApprox guard body n)
      (fun _ h₁ _ h₂ => I h₁ h₂ ∧ guard h₁ = false ∧ guard h₂ = false) :=
  rHoare_whileApprox hguard hbody n

end CatCrypt.NonUniform
