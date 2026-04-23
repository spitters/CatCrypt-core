/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Unary.Judgment
import CatCrypt.Prob.Support

/-!
# Unary Probabilistic Hoare Logic - Proof Rules

This file provides proof rules for the unary probabilistic Hoare logic.

## Main theorems

* `pHoare_ret` - Return rule: pure values satisfy postconditions derivable from precondition
* `pHoare_fail` - Fail rule: fail satisfies any postcondition (vacuously)
* `pHoare_sample` - Sample rule: if Q holds for all sampled values, the judgment holds
* `pHoare_get` - Get rule: reading from a location
* `pHoare_set` - Set rule: writing to a location
* `pHoare_bind` - Bind rule: sequential composition
* `pHoare_assert` - Assert rule: assertion with continuation

## Implementation notes

The key proof technique is extracting information from support membership.
For `SDistr.pure x`, the only element with nonzero probability is `x` itself.
We use `SDistr.mem_support_pure_iff` which states `b ∈ (pure a).support ↔ a = b`
without requiring `DecidableEq`.

For `SDistr.bind`, the challenge is that if `(d.bind f)(some y) ≠ 0` then
there must exist some `x` with `d(some x) ≠ 0` and `(f x)(some y) ≠ 0`.
This requires analyzing the sum `∑ x, d(x) * (f x)(y)` which is nonzero
only if at least one term is nonzero.
-/

namespace CatCrypt.Unary

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

variable {α β γ : Type*}

/-! ## Return rules -/

/-- Return rule: pure values satisfy any postcondition derivable from precondition.

For `SPComp.pure a`, the only outcome is `(a, h₀)` where `h₀` is the initial heap.
So we need `Q a h₀` which follows from the hypothesis. -/
theorem pHoare_ret {P : UPre} {a : α} {Q : UPost α}
    (h : ∀ h₀, P h₀ → Q a h₀) :
    pHoare P (SPComp.pure a) Q := by
  intro h₀ hP a' h' hsupp
  -- (SPComp.pure a) h₀ = SDistr.pure (a, h₀)
  -- hsupp : SDistr.pure (a, h₀) (some (a', h')) ≠ 0
  -- By mem_support_pure_iff, this means (a, h₀) = (a', h')
  simp only [SPComp.pure] at hsupp
  have hmem : (a', h') ∈ (SDistr.pure (a, h₀)).support :=
    hsupp
  rw [SDistr.mem_support_pure_iff] at hmem
  -- hmem : (a, h₀) = (a', h')
  cases hmem
  exact h h₀ hP

/-! ## Fail rule -/

/-- Fail satisfies any postcondition (vacuously, since no outcomes exist).

`SPComp.fail` returns `SDistr.fail` which assigns probability 0 to all
`some` outcomes, so the support is empty and the universal quantification
is vacuously true. -/
theorem pHoare_fail {P : UPre} {Q : UPost α} :
    pHoare P (SPComp.fail : SPComp α) Q := by
  intro h₀ _ a h' hsupp
  simp only [SPComp.fail] at hsupp
  -- SDistr.fail (some (a, h')) = 0, contradicting hsupp
  exact absurd (SDistr.fail_apply_some (a, h')) hsupp

/-! ## Sample rule -/

/-- Sample rule: if Q holds for all possible sampled values, the judgment holds.

`SPComp.sample α` draws uniformly from `α` and does not change the heap.
So any outcome `(a, h')` in the support satisfies `h' = h₀`, and we need
`Q a h₀` for all `a`, which the hypothesis provides. -/
theorem pHoare_sample [Fintype α] [Nonempty α] {P : UPre} {Q : UPost α}
    (h : ∀ h₀ a, P h₀ → Q a h₀) :
    pHoare P (SPComp.sample α) Q := by
  intro h₀ hP a h' hsupp
  -- SPComp.sample α h₀ = (SDistr.uniform α).bind (fun a => SDistr.pure (a, h₀))
  simp only [SPComp.sample] at hsupp
  -- Extract witness: ∃ a', uniform(a') ≠ 0 ∧ pure(a', h₀)(some (a, h')) ≠ 0
  obtain ⟨a', _, hpure⟩ := SDistr.bind_support_witness hsupp
  -- hpure : SDistr.pure (a', h₀) (some (a, h')) ≠ 0
  -- By mem_support_pure_iff: (a', h₀) = (a, h')
  have hmem : (a, h') ∈ (SDistr.pure (a', h₀)).support := hpure
  rw [SDistr.mem_support_pure_iff] at hmem
  -- hmem : (a', h₀) = (a, h')
  cases hmem
  exact h h₀ _ hP

/-! ## State rules -/

/-- Get rule: reading from a location.

`SPComp.get l` returns `SDistr.pure (h₀.get l, h₀)`, so the only outcome
is `(h₀.get l, h₀)`. -/
theorem pHoare_get {P : UPre} {l : Location} {Q : UPost l.ty}
    (h : ∀ h₀, P h₀ → Q (h₀.get l) h₀) :
    pHoare P (SPComp.get l) Q := by
  intro h₀ hP a h' hsupp
  -- (SPComp.get l) h₀ = SDistr.pure (h₀.get l, h₀)
  simp only [SPComp.get] at hsupp
  have hmem : (a, h') ∈ (SDistr.pure (h₀.get l, h₀)).support :=
    hsupp
  rw [SDistr.mem_support_pure_iff] at hmem
  -- hmem : (h₀.get l, h₀) = (a, h')
  cases hmem
  exact h h₀ hP

/-- Set rule: writing to a location.

`SPComp.set l v` returns `SDistr.pure ((), h₀.set l v)`, so the only outcome
is `((), h₀.set l v)`. -/
theorem pHoare_set {P : UPre} {l : Location} {v : l.ty} {Q : UPost Unit}
    (h : ∀ h₀, P h₀ → Q () (h₀.set l v)) :
    pHoare P (SPComp.set l v) Q := by
  intro h₀ hP a h' hsupp
  simp only [SPComp.set] at hsupp
  have hmem : (a, h') ∈ (SDistr.pure ((), h₀.set l v)).support :=
    hsupp
  rw [SDistr.mem_support_pure_iff] at hmem
  -- hmem : ((), h₀.set l v) = (a, h')
  cases hmem
  exact h h₀ hP

/-! ## Bind rule -/

/-- Bind rule: sequential composition.

This is the most important structural rule. To prove `pHoare P (c.bind f) Q`,
we need an intermediate postcondition `Mid` such that:
- `c` establishes `Mid` from `P`
- For each intermediate result `a`, `f a` establishes `Q` from `Mid a`

The key proof obligation is: if `(c h₀).bind (fun (a, h₁) => f a h₁)` assigns
nonzero probability to `(b, h')`, then there exists an intermediate `(a, h₁)`
with nonzero probability in `c h₀` such that `f a h₁` assigns nonzero
probability to `(b, h')`. This follows from the fact that a sum of nonneg
terms is nonzero iff at least one term is nonzero. -/
theorem pHoare_bind {P : UPre} {Mid : UPost α} {Q : UPost β}
    {c : SPComp α} {f : α → SPComp β}
    (hc : pHoare P c Mid)
    (hf : ∀ a, pHoare (Mid a) (f a) Q) :
    pHoare P (SPComp.bind c f) Q := by
  intro h₀ hP b h' hsupp
  -- SPComp.bind c f h₀ = (c h₀).bind (fun (a, h₁) => f a h₁)
  simp only [SPComp.bind] at hsupp
  -- Extract intermediate witness from bind support
  obtain ⟨a, h₁, hc_supp, hf_supp⟩ := SDistr.bind_support_witness_pair hsupp
  -- hc_supp : (c h₀)(some (a, h₁)) ≠ 0  — a is in support of c
  -- hf_supp : (f a h₁)(some (b, h')) ≠ 0 — (b, h') is in support of f a
  -- By hc, the intermediate state satisfies Mid
  have hMid : Mid a h₁ := hc h₀ hP a h₁ hc_supp
  -- By hf, the final state satisfies Q
  exact hf a h₁ hMid b h' hf_supp

/-! ## Assert rule -/

/-- Assert rule: if precondition implies the assertion, continue.

`SPComp.assert p` is `if p then pure () else fail`. When `p` holds
(which it does, given `P` implies `p`), it reduces to `pure ()`. -/
theorem pHoare_assert {P : UPre} {Q : UPost Unit} {p : Prop} [Decidable p]
    (hp : ∀ h₀, P h₀ → p)
    (hQ : ∀ h₀, P h₀ → Q () h₀) :
    pHoare P (SPComp.assert p) Q := by
  intro h₀ hP a h' hsupp
  simp only [SPComp.assert, hp h₀ hP, ↓reduceIte] at hsupp
  -- After reduction, this is SPComp.pure () applied to h₀
  -- hsupp : SDistr.pure ((), h₀) (some (a, h')) ≠ 0
  have hmem : (a, h') ∈ (SDistr.pure ((), h₀)).support :=
    hsupp
  rw [SDistr.mem_support_pure_iff] at hmem
  cases hmem
  exact hQ h₀ hP

/-! ## Derived rules -/

/-- Frame rule: pHoare is preserved under conjunction with a frame condition.

If `c` preserves `R` (i.e., `R` holds before and after), and we have
`pHoare P c Q`, then we can add `R` to both pre- and postcondition. -/
theorem pHoare_frame {P : UPre} {Q : UPost α} {R : Heap → Prop}
    {c : SPComp α}
    (hPQ : pHoare P c Q)
    (hR : pHoare P c (fun _ h' => R h')) :
    pHoare (fun h => P h ∧ R h) c (fun a h' => Q a h' ∧ R h') := by
  intro h₀ ⟨hP, _⟩ a h' hsupp
  exact ⟨hPQ h₀ hP a h' hsupp, hR h₀ hP a h' hsupp⟩

/-- Existential rule: if for some witness the judgment holds, the judgment holds. -/
theorem pHoare_exists {P : β → UPre} {Q : UPost α} {c : SPComp α}
    (h : ∀ b, pHoare (P b) c Q) :
    pHoare (fun h₀ => ∃ b, P b h₀) c Q := by
  intro h₀ ⟨b, hPb⟩ a h' hsupp
  exact h b h₀ hPb a h' hsupp

/-- Weakening the return rule: if we know the exact return value -/
theorem pHoare_ret_eq {P : UPre} {a : α} :
    pHoare P (SPComp.pure a) (fun a' h' => ∃ h₀, P h₀ ∧ a' = a ∧ h' = h₀) := by
  apply pHoare_ret
  intro h₀ hP
  exact ⟨h₀, hP, rfl, rfl⟩

end CatCrypt.Unary
