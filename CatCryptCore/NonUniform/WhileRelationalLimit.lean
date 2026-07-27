/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.NonUniform.While
import CatCryptCore.NonUniform.WhileRelational

/-!
# The pRHL rule for the unbounded loop

`rHoare_whileLoop` relates `whileLoop guard₁ body₁` to `whileLoop guard₂ body₂`
under the hypotheses of the fixed-budget rule `rHoare_whileApprox`: a relational
invariant `I` that makes the two guards agree, and two bodies that preserve `I`
from any `I`-related pair of heaps at which the guards hold.

The judgment at a fixed budget only produces a coupling of the two approximants
at that budget, and couplings at different budgets need not be comparable. The
rule at the loop is proved by building one non-decreasing family of couplings
`loopJoint` and taking its limit: a chosen coupling `bodyJoint` of the two bodies
is threaded through the recursion on the budget, so the coupling at budget `n` is
a restriction of the coupling at budget `n + 1`.

## Main definitions

* `loopJoint guard₁ bj n h₁ h₂` — the joint distribution of the lockstep run of
  the two loops for at most `n` iterations, with `bj` coupling one execution of
  the two bodies
* `bodyJoint hbody h₁ h₂` — a coupling of the two bodies chosen from the body
  judgment
* `loopJointLim hbody h₁ h₂` — the limit of `loopJoint guard₁ (bodyJoint hbody)`
  over the budget

## Main results

* `loopJoint_mono` — the family is non-decreasing in the budget
* `loopJoint_bind_fst`, `loopJoint_bind_snd` — the two marginals of the family at
  budget `n` are the two approximants at budget `n`
* `loopJoint_support` — every coupled pair at any budget satisfies `I` with both
  guards false
* `rHoare_whileLoop` — the synchronous invariant rule at the unbounded loop
-/

set_option autoImplicit false

namespace CatCrypt.NonUniform

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational

/-! ## Support of a bind -/

/-- A value of nonzero weight under a bind comes from a value of nonzero weight
under the bound distribution. -/
theorem exists_ne_zero_of_bind_apply_ne_zero {α β : Type*} {d : SDistr α}
    {f : α → SDistr β} {b : β} (hne : (d.bind f) (some b) ≠ 0) :
    ∃ a, d (some a) ≠ 0 ∧ f a (some b) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hne ?_
  rw [bind_apply_some]
  refine ENNReal.tsum_eq_zero.mpr fun a => ?_
  by_cases ha : d (some a) = 0
  · rw [ha, zero_mul]
  · rw [hcon a ha, mul_zero]

/-! ## The joint distribution of a budgeted lockstep run -/

/-- The joint distribution of the lockstep run of two loops at budget `n`: while
the left guard holds, `bj` couples one execution of the two bodies and the
remaining budget is spent from the two resulting heaps. -/
noncomputable def loopJoint (guard₁ : Heap → Bool)
    (bj : Heap → Heap → SDistr ((Unit × Heap) × (Unit × Heap))) :
    ℕ → Heap → Heap → SDistr ((Unit × Heap) × (Unit × Heap))
  | 0, _, _ => SDistr.fail
  | n + 1, h₁, h₂ =>
      if guard₁ h₁ then
        (bj h₁ h₂).bind fun pq => loopJoint guard₁ bj n pq.1.2 pq.2.2
      else
        SDistr.pure (((), h₁), ((), h₂))

@[simp] theorem loopJoint_zero (guard₁ : Heap → Bool)
    (bj : Heap → Heap → SDistr ((Unit × Heap) × (Unit × Heap))) (h₁ h₂ : Heap) :
    loopJoint guard₁ bj 0 h₁ h₂ = SDistr.fail := rfl

theorem loopJoint_succ (guard₁ : Heap → Bool)
    (bj : Heap → Heap → SDistr ((Unit × Heap) × (Unit × Heap))) (n : ℕ) (h₁ h₂ : Heap) :
    loopJoint guard₁ bj (n + 1) h₁ h₂ =
      if guard₁ h₁ then (bj h₁ h₂).bind fun pq => loopJoint guard₁ bj n pq.1.2 pq.2.2
      else SDistr.pure (((), h₁), ((), h₂)) := rfl

theorem loopJoint_succ_of_guard {guard₁ : Heap → Bool}
    (bj : Heap → Heap → SDistr ((Unit × Heap) × (Unit × Heap))) {h₁ : Heap}
    (hg : guard₁ h₁ = true) (n : ℕ) (h₂ : Heap) :
    loopJoint guard₁ bj (n + 1) h₁ h₂
      = (bj h₁ h₂).bind fun pq => loopJoint guard₁ bj n pq.1.2 pq.2.2 := by
  rw [loopJoint_succ, if_pos hg]

theorem loopJoint_succ_of_not_guard {guard₁ : Heap → Bool}
    (bj : Heap → Heap → SDistr ((Unit × Heap) × (Unit × Heap))) {h₁ : Heap}
    (hg : guard₁ h₁ = false) (n : ℕ) (h₂ : Heap) :
    loopJoint guard₁ bj (n + 1) h₁ h₂ = SDistr.pure (((), h₁), ((), h₂)) := by
  rw [loopJoint_succ, if_neg (by simp [hg])]

/-! ## The family is non-decreasing in the budget -/

/-- Raising the budget by one does not decrease the weight of a coupled pair. -/
theorem loopJoint_apply_le_succ (guard₁ : Heap → Bool)
    (bj : Heap → Heap → SDistr ((Unit × Heap) × (Unit × Heap))) :
    ∀ (n : ℕ) (h₁ h₂ : Heap) (x : (Unit × Heap) × (Unit × Heap)),
      loopJoint guard₁ bj n h₁ h₂ (some x) ≤ loopJoint guard₁ bj (n + 1) h₁ h₂ (some x)
  | 0, _, _, x => by
      rw [loopJoint_zero, SDistr.fail_apply_some]
      exact zero_le
  | n + 1, h₁, h₂, x => by
      cases hg : guard₁ h₁ with
      | false =>
          rw [loopJoint_succ_of_not_guard bj hg, loopJoint_succ_of_not_guard bj hg]
      | true =>
          rw [loopJoint_succ_of_guard bj hg, loopJoint_succ_of_guard bj hg]
          exact SDistr.bind_apply_mono _ _ fun pq =>
            loopJoint_apply_le_succ guard₁ bj n pq.1.2 pq.2.2 x

/-- The weight of a coupled pair is non-decreasing in the budget. -/
theorem loopJoint_mono (guard₁ : Heap → Bool)
    (bj : Heap → Heap → SDistr ((Unit × Heap) × (Unit × Heap))) (h₁ h₂ : Heap) :
    MonoSeq fun n => loopJoint guard₁ bj n h₁ h₂ := by
  intro n m hnm x
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact ih.trans (loopJoint_apply_le_succ guard₁ bj m h₁ h₂ x)

/-! ## A chosen coupling of the two bodies -/

variable {guard₁ guard₂ : Heap → Bool} {body₁ body₂ : SPComp Unit} {I : RPre}

/-- The body judgment supplies, at every pair of heaps, a distribution that is a
coupling of the two bodies supported in the invariant whenever the invariant
holds and both guards are true. -/
theorem exists_bodyJoint
    (hbody : rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard₁ h₁ = true ∧ guard₂ h₂ = true)
      body₁ body₂ (fun _ h₁ _ h₂ => I h₁ h₂)) (h₁ h₂ : Heap) :
    ∃ d : SDistr ((Unit × Heap) × (Unit × Heap)),
      I h₁ h₂ → guard₁ h₁ = true → guard₂ h₂ = true →
        (∀ p, (d.bind fun q => SDistr.pure q.1) (some p) = body₁ h₁ (some p)) ∧
        (∀ p, (d.bind fun q => SDistr.pure q.2) (some p) = body₂ h₂ (some p)) ∧
        (∀ p q, d (some (p, q)) ≠ 0 → I p.2 q.2) := by
  by_cases hpre : I h₁ h₂ ∧ guard₁ h₁ = true ∧ guard₂ h₂ = true
  · obtain ⟨c, hc⟩ := hbody h₁ h₂ hpre
    exact ⟨c.joint, fun _ _ _ => ⟨c.left_marginal, c.right_marginal, hc⟩⟩
  · exact ⟨SDistr.fail, fun hI hg₁ hg₂ => absurd ⟨hI, hg₁, hg₂⟩ hpre⟩

/-- A coupling of the two bodies chosen from the body judgment. -/
noncomputable def bodyJoint
    (hbody : rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard₁ h₁ = true ∧ guard₂ h₂ = true)
      body₁ body₂ (fun _ h₁ _ h₂ => I h₁ h₂)) (h₁ h₂ : Heap) :
    SDistr ((Unit × Heap) × (Unit × Heap)) :=
  (exists_bodyJoint hbody h₁ h₂).choose

/-- At a pair of heaps satisfying the invariant with both guards true, the chosen
distribution has the two bodies as marginals and is supported in the invariant. -/
theorem bodyJoint_spec
    (hbody : rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard₁ h₁ = true ∧ guard₂ h₂ = true)
      body₁ body₂ (fun _ h₁ _ h₂ => I h₁ h₂)) {h₁ h₂ : Heap}
    (hI : I h₁ h₂) (hg₁ : guard₁ h₁ = true) (hg₂ : guard₂ h₂ = true) :
    (∀ p, ((bodyJoint hbody h₁ h₂).bind fun q => SDistr.pure q.1) (some p)
        = body₁ h₁ (some p)) ∧
      (∀ p, ((bodyJoint hbody h₁ h₂).bind fun q => SDistr.pure q.2) (some p)
        = body₂ h₂ (some p)) ∧
      (∀ p q, bodyJoint hbody h₁ h₂ (some (p, q)) ≠ 0 → I p.2 q.2) :=
  (exists_bodyJoint hbody h₁ h₂).choose_spec hI hg₁ hg₂

/-! ## The marginals of the family -/

/-- The left marginal of the coupling at budget `n` is the left approximant at
budget `n`. -/
theorem loopJoint_bind_fst
    (hguard : ∀ h₁ h₂, I h₁ h₂ → guard₁ h₁ = guard₂ h₂)
    (hbody : rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard₁ h₁ = true ∧ guard₂ h₂ = true)
      body₁ body₂ (fun _ h₁ _ h₂ => I h₁ h₂)) :
    ∀ (n : ℕ) (h₁ h₂ : Heap), I h₁ h₂ →
      ((loopJoint guard₁ (bodyJoint hbody) n h₁ h₂).bind fun q => SDistr.pure q.1)
        = whileApprox guard₁ body₁ n h₁ := by
  intro n
  induction n with
  | zero =>
      intro h₁ _ _
      rw [loopJoint_zero, SDistr.bind_fail]
      rfl
  | succ n ih =>
      intro h₁ h₂ hI
      cases hg₁ : guard₁ h₁ with
      | false =>
          rw [loopJoint_succ_of_not_guard _ hg₁, SDistr.pure_bind,
            whileApprox_succ_of_not_guard hg₁]
          rfl
      | true =>
          have hg₂ : guard₂ h₂ = true := by rw [← hguard h₁ h₂ hI]; exact hg₁
          obtain ⟨hm₁, _, hsup⟩ := bodyJoint_spec hbody hI hg₁ hg₂
          have hmarg : ((bodyJoint hbody h₁ h₂).bind fun q => SDistr.pure q.1) = body₁ h₁ :=
            SDistr.eq_of_some_eq hm₁
          rw [loopJoint_succ_of_guard _ hg₁, whileApprox_succ_bind_of_guard hg₁,
            SDistr.bind_assoc, ← hmarg, SDistr.bind_assoc]
          refine SDistr.bind_congr_support fun pq hne => ?_
          rw [SDistr.pure_bind]
          exact ih pq.1.2 pq.2.2 (hsup pq.1 pq.2 hne)

/-- The right marginal of the coupling at budget `n` is the right approximant at
budget `n`. -/
theorem loopJoint_bind_snd
    (hguard : ∀ h₁ h₂, I h₁ h₂ → guard₁ h₁ = guard₂ h₂)
    (hbody : rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard₁ h₁ = true ∧ guard₂ h₂ = true)
      body₁ body₂ (fun _ h₁ _ h₂ => I h₁ h₂)) :
    ∀ (n : ℕ) (h₁ h₂ : Heap), I h₁ h₂ →
      ((loopJoint guard₁ (bodyJoint hbody) n h₁ h₂).bind fun q => SDistr.pure q.2)
        = whileApprox guard₂ body₂ n h₂ := by
  intro n
  induction n with
  | zero =>
      intro _ _ _
      rw [loopJoint_zero, SDistr.bind_fail]
      rfl
  | succ n ih =>
      intro h₁ h₂ hI
      cases hg₁ : guard₁ h₁ with
      | false =>
          have hg₂ : guard₂ h₂ = false := by rw [← hguard h₁ h₂ hI]; exact hg₁
          rw [loopJoint_succ_of_not_guard _ hg₁, SDistr.pure_bind,
            whileApprox_succ_of_not_guard hg₂]
          rfl
      | true =>
          have hg₂ : guard₂ h₂ = true := by rw [← hguard h₁ h₂ hI]; exact hg₁
          obtain ⟨_, hm₂, hsup⟩ := bodyJoint_spec hbody hI hg₁ hg₂
          have hmarg : ((bodyJoint hbody h₁ h₂).bind fun q => SDistr.pure q.2) = body₂ h₂ :=
            SDistr.eq_of_some_eq hm₂
          rw [loopJoint_succ_of_guard _ hg₁, whileApprox_succ_bind_of_guard hg₂,
            SDistr.bind_assoc, ← hmarg, SDistr.bind_assoc]
          refine SDistr.bind_congr_support fun pq hne => ?_
          rw [SDistr.pure_bind]
          exact ih pq.1.2 pq.2.2 (hsup pq.1 pq.2 hne)

/-! ## The support of the family -/

/-- Every pair coupled at any budget satisfies the invariant with both guards
false. -/
theorem loopJoint_support
    (hguard : ∀ h₁ h₂, I h₁ h₂ → guard₁ h₁ = guard₂ h₂)
    (hbody : rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard₁ h₁ = true ∧ guard₂ h₂ = true)
      body₁ body₂ (fun _ h₁ _ h₂ => I h₁ h₂)) :
    ∀ (n : ℕ) (h₁ h₂ : Heap), I h₁ h₂ → ∀ p q : Unit × Heap,
      loopJoint guard₁ (bodyJoint hbody) n h₁ h₂ (some (p, q)) ≠ 0 →
        I p.2 q.2 ∧ guard₁ p.2 = false ∧ guard₂ q.2 = false := by
  intro n
  induction n with
  | zero =>
      intro h₁ h₂ _ p q hne
      rw [loopJoint_zero] at hne
      exact absurd (SDistr.fail_apply_some (p, q)) hne
  | succ n ih =>
      intro h₁ h₂ hI p q hne
      cases hg₁ : guard₁ h₁ with
      | false =>
          have hg₂ : guard₂ h₂ = false := by rw [← hguard h₁ h₂ hI]; exact hg₁
          rw [loopJoint_succ_of_not_guard _ hg₁] at hne
          have heq : (((), h₁), ((), h₂)) = (p, q) :=
            (SDistr.mem_support_pure_iff _ (p, q)).mp hne
          simp only [Prod.mk.injEq] at heq
          obtain ⟨hp, hq⟩ := heq
          subst hp
          subst hq
          exact ⟨hI, hg₁, hg₂⟩
      | true =>
          have hg₂ : guard₂ h₂ = true := by rw [← hguard h₁ h₂ hI]; exact hg₁
          rw [loopJoint_succ_of_guard _ hg₁] at hne
          obtain ⟨pq, hpq, hrest⟩ := exists_ne_zero_of_bind_apply_ne_zero hne
          obtain ⟨_, _, hsup⟩ := bodyJoint_spec hbody hI hg₁ hg₂
          exact ih pq.1.2 pq.2.2 (hsup pq.1 pq.2 hpq) p q hrest

/-! ## The limit of the family -/

/-- The limit over the budget of the couplings of the two loops. -/
noncomputable def loopJointLim
    (hbody : rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard₁ h₁ = true ∧ guard₂ h₂ = true)
      body₁ body₂ (fun _ h₁ _ h₂ => I h₁ h₂)) (h₁ h₂ : Heap) :
    SDistr ((Unit × Heap) × (Unit × Heap)) :=
  mlim (fun n => loopJoint guard₁ (bodyJoint hbody) n h₁ h₂)
    (loopJoint_mono guard₁ (bodyJoint hbody) h₁ h₂)

/-- A pair coupled in the limit is coupled at some budget. -/
theorem exists_loopJoint_ne_zero
    {hbody : rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard₁ h₁ = true ∧ guard₂ h₂ = true)
      body₁ body₂ (fun _ h₁ _ h₂ => I h₁ h₂)} {h₁ h₂ : Heap}
    {x : (Unit × Heap) × (Unit × Heap)} (hne : loopJointLim hbody h₁ h₂ (some x) ≠ 0) :
    ∃ n, loopJoint guard₁ (bodyJoint hbody) n h₁ h₂ (some x) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hne ?_
  simp only [loopJointLim, mlim_apply_some]
  simpa using iSup_eq_bot.mpr hcon

/-- The left marginal of the limit is the left loop. -/
theorem loopJointLim_bind_fst
    (hguard : ∀ h₁ h₂, I h₁ h₂ → guard₁ h₁ = guard₂ h₂)
    (hbody : rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard₁ h₁ = true ∧ guard₂ h₂ = true)
      body₁ body₂ (fun _ h₁ _ h₂ => I h₁ h₂)) {h₁ h₂ : Heap} (hI : I h₁ h₂)
    (p : Unit × Heap) :
    ((loopJointLim hbody h₁ h₂).bind fun q => SDistr.pure q.1) (some p)
      = whileLoop guard₁ body₁ h₁ (some p) := by
  simp only [loopJointLim]
  rw [mlim_bind, mlim_apply_some, whileLoop_apply_some]
  exact iSup_congr fun n => by rw [loopJoint_bind_fst hguard hbody n h₁ h₂ hI]

/-- The right marginal of the limit is the right loop. -/
theorem loopJointLim_bind_snd
    (hguard : ∀ h₁ h₂, I h₁ h₂ → guard₁ h₁ = guard₂ h₂)
    (hbody : rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard₁ h₁ = true ∧ guard₂ h₂ = true)
      body₁ body₂ (fun _ h₁ _ h₂ => I h₁ h₂)) {h₁ h₂ : Heap} (hI : I h₁ h₂)
    (p : Unit × Heap) :
    ((loopJointLim hbody h₁ h₂).bind fun q => SDistr.pure q.2) (some p)
      = whileLoop guard₂ body₂ h₂ (some p) := by
  simp only [loopJointLim]
  rw [mlim_bind, mlim_apply_some, whileLoop_apply_some]
  exact iSup_congr fun n => by rw [loopJoint_bind_snd hguard hbody n h₁ h₂ hI]

/-! ## The rule -/

/--
The synchronous invariant rule for the unbounded loop.

If the relational invariant `I` forces the two guards to agree, and the two
bodies preserve `I` from any `I`-related pair of heaps at which the guards hold,
then the two loops are related by `I` together with both guards being false.
-/
theorem rHoare_whileLoop
    (hguard : ∀ h₁ h₂, I h₁ h₂ → guard₁ h₁ = guard₂ h₂)
    (hbody : rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard₁ h₁ = true ∧ guard₂ h₂ = true)
      body₁ body₂ (fun _ h₁ _ h₂ => I h₁ h₂)) :
    rHoare I (whileLoop guard₁ body₁) (whileLoop guard₂ body₂)
      (fun _ h₁ _ h₂ => I h₁ h₂ ∧ guard₁ h₁ = false ∧ guard₂ h₂ = false) := by
  intro h₁ h₂ hI
  refine ⟨⟨loopJointLim hbody h₁ h₂, loopJointLim_bind_fst hguard hbody hI,
    loopJointLim_bind_snd hguard hbody hI⟩, ?_⟩
  intro p q hne
  obtain ⟨n, hn⟩ := exists_loopJoint_ne_zero hne
  exact loopJoint_support hguard hbody n h₁ h₂ hI p q hn

/-- The rule with one guard and one body on both sides. -/
theorem rHoare_whileLoop_same {guard : Heap → Bool} {body : SPComp Unit} {I : RPre}
    (hguard : ∀ h₁ h₂, I h₁ h₂ → guard h₁ = guard h₂)
    (hbody : rHoare (fun h₁ h₂ => I h₁ h₂ ∧ guard h₁ = true ∧ guard h₂ = true)
      body body (fun _ h₁ _ h₂ => I h₁ h₂)) :
    rHoare I (whileLoop guard body) (whileLoop guard body)
      (fun _ h₁ _ h₂ => I h₁ h₂ ∧ guard h₁ = false ∧ guard h₂ = false) :=
  rHoare_whileLoop hguard hbody

end CatCrypt.NonUniform
