/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Prob.Support
public import CatCryptCore.Core.StdDoBridge
public import CatCryptCore.XDijkstra.Rel.XSDistrSoundness
public import CatCryptCore.XDijkstra.XMvcgenReg
public import CatCryptCore.XDijkstra.GradedDo

@[expose] public section
set_option autoImplicit false

/-!
# `XErrMonad`: sub-distributions graded by a bound on the failure weight

`SDistr α` is `PMF (Option α)`, and the weight `d none` is the probability that
the computation `d` fails; it equals `1 - SDistr.mass d` (`one_sub_mass`).
`ErrM ε α` is the type of sub-distributions whose failure weight is at most `ε`.
The family is a graded monad over `(ℝ≥0∞, +, 0)`: `ErrM.pure` has index `0`, and
`ErrM.bind` adds the indices, by the union bound `sdistr_bind_none_le`. The grade
is the failure weight and not a bound on the mass from below, because the failure
weight of a bind is the sum
`d none + ∑' a, d (some a) * f a none` (`sdistr_bind_none_eq`), which is additive
in the two bounds, while the mass of a bind is bounded by a product.

For each index `ε` the type constructor `ErrM ε` has an `XWP` instance at the
shape `.graded ℝ≥0∞ .pure`. The weakest precondition is the support-level
observation `sdistrWP` of the underlying sub-distribution: the postcondition
holds at every value of nonzero weight. The grade of the transformer is the
index `ε`.

## Main definitions

* `ErrM`: the indexed family, with `ErrM.dist` and the invariant `ErrM.fail_le`.
* `ErrM.pure`, `ErrM.bind`, `ErrM.seq`, `ErrM.relax`, `ErrM.ofSDistr`: the
  operations.
* `ErrM.instGradedMonad`, `ErrM.instLawfulGradedMonad`: the family as a lawful
  graded monad, so programs are written as `gdo` blocks.
* `psErr`: the shape `.graded ℝ≥0∞ .pure`.
* `errWP`, `instXWPErrM`: the observation.

## Main results

* `sdistr_bind_none_eq`, `sdistr_bind_none_le`: the failure weight of a bind, and
  the union bound.
* `errWP_triple_iff`: an `XTriple` over `ErrM ε` is the support-level Hoare
  triple of the sub-distribution.
* `ErrM.sound`: from a triple and a bound `b` on the grade, every value of
  nonzero weight satisfies the postcondition and the failure weight is at most
  `b`.
* `ErrM.prob_post_ge`: under the same hypotheses the total weight of the values
  that satisfy the postcondition is at least `1 - b`.
* `errWP_pure`, `errWP_bind`, `errWP_seq`, `errWP_bind_grade_fst`: the
  observation sends `ErrM.pure` to `xpure` and `ErrM.seq` to `xseq`, agrees with
  `xbind` on weakest preconditions, and sends the index of `ErrM.bind` to the sum
  of the grades.
* `errWP_seq_grade_le`: the budget rule `xtriple_grade_le` for two sequenced
  programs.
* `xwp_errM`, `errWP_apply`, `errWP_apply_pure`, `errWP_apply_bind`,
  `errWP_apply_seq`, `errWP_apply_relax`, `errWP_grade_fst`, `ErrM.gpure_eq`,
  `ErrM.gbind_eq` and `ErrM.gseq_eq` are in the `xspec` set: `xmvcgen!` reduces a
  triple about a `gdo` block to a statement about the supports of its steps.
-/

namespace CatCrypt.XDijkstra

open scoped ENNReal
open CatCrypt.Prob

variable {α β γ : Type}

/-! ## The failure weight of a bind -/

/-- The failure weight is the complement of the mass. -/
theorem one_sub_mass (d : SDistr α) : 1 - SDistr.mass d = d none :=
  ENNReal.sub_sub_cancel ENNReal.one_ne_top (PMF.coe_le_one d none)

/-- The failure weight of a bind: the failure weight of the head, and for each
value of the head its weight times the failure weight of the continuation. -/
theorem sdistr_bind_none_eq (d : SDistr α) (f : α → SDistr β) :
    (d.bind f) none = d none + ∑' a, d (some a) * f a none := by
  rw [SDistr.bind, PMF.bind_apply, SDistr.tsum_option_eq_add]
  simp only [SDistr.fail_apply_none, mul_one]

/-- The union bound for a bind: if the head fails with weight at most `ε₁` and
every continuation with weight at most `ε₂`, the bind fails with weight at most
`ε₁ + ε₂`. -/
theorem sdistr_bind_none_le {d : SDistr α} {f : α → SDistr β} {ε₁ ε₂ : ℝ≥0∞}
    (hd : d none ≤ ε₁) (hf : ∀ a, f a none ≤ ε₂) :
    (d.bind f) none ≤ ε₁ + ε₂ := by
  rw [sdistr_bind_none_eq]
  refine add_le_add hd ?_
  calc ∑' a, d (some a) * f a none
      ≤ ∑' a, d (some a) * ε₂ := ENNReal.tsum_le_tsum fun a => by gcongr; exact hf a
    _ = (∑' a, d (some a)) * ε₂ := ENNReal.tsum_mul_right
    _ ≤ 1 * ε₂ := by gcongr; exact SDistr.tsum_some_le_one d
    _ = ε₂ := one_mul _

/-! ## The indexed family -/

/-- A sub-distribution whose failure weight is at most the index `ε`. -/
structure ErrM (ε : ℝ≥0∞) (α : Type) where
  /-- The underlying sub-distribution. -/
  dist : SDistr α
  /-- The failure weight is at most the index. -/
  fail_le : dist none ≤ ε

namespace ErrM

variable {ε ε₁ ε₂ ε₃ : ℝ≥0∞}

/-- Return a value: the point distribution, which does not fail. -/
protected noncomputable def pure (a : α) : ErrM 0 α where
  dist := SDistr.pure a
  fail_le := (SDistr.pure_apply_none a).le

/-- Run `x`, then the continuation at its value. The bounds on the failure weight
add. -/
protected noncomputable def bind (x : ErrM ε₁ α) (f : α → ErrM ε₂ β) : ErrM (ε₁ + ε₂) β where
  dist := x.dist.bind fun a => (f a).dist
  fail_le := sdistr_bind_none_le x.fail_le fun a => (f a).fail_le

/-- Run `x`, discard its value, then run `y`. -/
protected noncomputable def seq (x : ErrM ε₁ α) (y : ErrM ε₂ β) : ErrM (ε₁ + ε₂) β :=
  x.bind fun _ => y

/-- The same sub-distribution at a larger index. -/
def relax (h : ε₁ ≤ ε₂) (x : ErrM ε₁ α) : ErrM ε₂ α where
  dist := x.dist
  fail_le := x.fail_le.trans h

/-- A sub-distribution, at the index that is its failure weight. -/
def ofSDistr (d : SDistr α) : ErrM (d none) α where
  dist := d
  fail_le := le_rfl

/-! ### The sub-distribution of each operation -/

/-- The sub-distribution of `ErrM.pure`. -/
@[simp, xspec] theorem dist_pure (a : α) : (ErrM.pure a).dist = SDistr.pure a := rfl

/-- The sub-distribution of `ErrM.bind`. -/
@[simp, xspec] theorem dist_bind (x : ErrM ε₁ α) (f : α → ErrM ε₂ β) :
    (x.bind f).dist = x.dist.bind fun a => (f a).dist := rfl

/-- The sub-distribution of `ErrM.seq`. -/
@[simp, xspec] theorem dist_seq (x : ErrM ε₁ α) (y : ErrM ε₂ β) :
    (x.seq y).dist = x.dist.bind fun _ => y.dist := rfl

/-- The sub-distribution of `ErrM.relax`. -/
@[simp, xspec] theorem dist_relax (h : ε₁ ≤ ε₂) (x : ErrM ε₁ α) :
    (x.relax h).dist = x.dist := rfl

/-- The sub-distribution of `ErrM.ofSDistr`. -/
@[simp, xspec] theorem dist_ofSDistr (d : SDistr α) : (ofSDistr d).dist = d := rfl

/-! ### The graded-monad instance -/

/-- `ErrM` is a graded monad over `(ℝ≥0∞, +, 0)`, so an `ErrM` program is written
as a `gdo` block. -/
noncomputable instance instGradedMonad : GradedMonad ℝ≥0∞ ErrM where
  gpure := ErrM.pure
  gbind := ErrM.bind

/-- `GradedMonad.gpure` at `ErrM` is `ErrM.pure`. -/
@[simp, xspec] theorem gpure_eq (a : α) : (GradedMonad.gpure a : ErrM 0 α) = ErrM.pure a := rfl

/-- `GradedMonad.gbind` at `ErrM` is `ErrM.bind`. -/
@[simp, xspec] theorem gbind_eq (x : ErrM ε₁ α) (f : α → ErrM ε₂ β) :
    GradedMonad.gbind x f = x.bind f := rfl

/-- `GradedMonad.gseq` at `ErrM` is `ErrM.seq`. -/
@[simp, xspec] theorem gseq_eq (x : ErrM ε₁ α) (y : ErrM ε₂ β) :
    GradedMonad.gseq x y = x.seq y := rfl

/-- Two programs at equal indices with the same sub-distribution are
heterogeneously equal. -/
theorem heq_of_dist_eq (h : ε₁ = ε₂) {x : ErrM ε₁ α} {y : ErrM ε₂ α}
    (hd : x.dist = y.dist) : HEq x y := by
  subst h
  cases x
  cases y
  cases hd
  rfl

/-- `ErrM` satisfies the laws of a graded monad; they are the monad laws of
`SDistr`. -/
instance instLawfulGradedMonad : LawfulGradedMonad ℝ≥0∞ ErrM where
  gpure_gbind a _ := heq_of_dist_eq (zero_add _) (SDistr.pure_bind a _)
  gbind_gpure x := heq_of_dist_eq (add_zero _) (SDistr.bind_pure x.dist)
  gbind_assoc x _ _ := heq_of_dist_eq (add_assoc _ _ _) (SDistr.bind_assoc x.dist _ _)

end ErrM

/-! ## The observation at the graded shape -/

section Observation

variable {ε ε₁ ε₂ : ℝ≥0∞}

/-- The shape of `ErrM ε`: a grade layer over `ℝ≥0∞` and no state. -/
abbrev psErr : XPostShape.{0} := .graded ℝ≥0∞ .pure

/-- The weakest-precondition observation of an `ErrM ε` program. The weakest
precondition is that of the support-level observation `sdistrWP` of the
underlying sub-distribution; the grade is the index `ε`, an upper bound on the
failure weight (`ErrM.fail_le`). -/
def errWP (x : ErrM ε α) : XPredTrans psErr Prop α where
  apply Q := (sdistrWP x.dist).apply Q
  grade := (ε, PUnit.unit)
  mono h := (sdistrWP x.dist).mono h

/-- `ErrM ε` observed as a transformer of grade `ε` over `Prop`. -/
instance instXWPErrM : XWP (ErrM ε) psErr Prop where
  xwp := errWP

/-- The observation of an `ErrM` program is `errWP`. -/
@[simp, xspec] theorem xwp_errM (x : ErrM ε α) :
    XWP.xwp (ps := psErr) (Ω := Prop) x = errWP x := rfl

/-- The weakest precondition of an `ErrM` program: the postcondition holds at
every value of nonzero weight. The simp priority is low, so the reductions of
`ErrM.pure`, `ErrM.bind`, `ErrM.seq` and `ErrM.relax` apply first and this
equation applies to the remaining steps. -/
@[simp low, xspec low] theorem errWP_apply (x : ErrM ε α) (Q : XPostCond α psErr Prop) :
    (errWP x).apply Q = ∀ a, x.dist (some a) ≠ 0 → Q.1 a := rfl

/-- The grade of the observation of an `ErrM ε` program is `ε`. -/
@[simp, xspec] theorem errWP_grade_fst (x : ErrM ε α) : (errWP x).grade.1 = ε := rfl

/-! ### The observation and the graded-monad operations -/

/-- The weakest precondition of `ErrM.pure` evaluates the postcondition at the
value. -/
@[simp, xspec] theorem errWP_apply_pure (a : α) (Q : XPostCond α psErr Prop) :
    (errWP (ErrM.pure a)).apply Q = Q.1 a := by
  refine propext ⟨fun h => h a ((SDistr.mem_support_pure_iff a a).mpr rfl), fun h b hb => ?_⟩
  obtain rfl := (SDistr.mem_support_pure_iff a b).mp hb
  exact h

/-- The weakest precondition of `ErrM.bind` is the weakest precondition of the
head at the weakest preconditions of the continuations. -/
@[simp, xspec] theorem errWP_apply_bind (x : ErrM ε₁ α) (f : α → ErrM ε₂ β)
    (Q : XPostCond β psErr Prop) :
    (errWP (x.bind f)).apply Q = (errWP x).apply (fun a => (errWP (f a)).apply Q, Q.2) := by
  refine propext ⟨fun h a ha b hb => ?_, fun h b hb => ?_⟩
  · exact h b ((SDistr.bind_apply_some_ne_zero_iff _ _ b).mpr ⟨a, ha, hb⟩)
  · obtain ⟨a, ha, hab⟩ := (SDistr.bind_apply_some_ne_zero_iff _ _ b).mp hb
    exact h a ha b hab

/-- The weakest precondition of `ErrM.seq` is the weakest precondition of the
first program at the weakest precondition of the second. -/
@[simp, xspec] theorem errWP_apply_seq (x : ErrM ε₁ α) (y : ErrM ε₂ β)
    (Q : XPostCond β psErr Prop) :
    (errWP (x.seq y)).apply Q = (errWP x).apply (fun _ => (errWP y).apply Q, Q.2) :=
  errWP_apply_bind x (fun _ => y) Q

/-- The weakest precondition of `ErrM.relax` is that of the program. -/
@[simp, xspec] theorem errWP_apply_relax (h : ε₁ ≤ ε₂) (x : ErrM ε₁ α)
    (Q : XPostCond α psErr Prop) :
    (errWP (x.relax h)).apply Q = (errWP x).apply Q := rfl

/-- Two transformers at the shape `psErr` with the same weakest preconditions and
the same grade are equal. -/
theorem xpredTrans_psErr_ext {s t : XPredTrans psErr Prop α}
    (ha : ∀ Q, s.apply Q = t.apply Q) (hg : s.grade = t.grade) : s = t := by
  cases s
  cases t
  obtain rfl : _ = _ := funext ha
  cases hg
  rfl

/-- The observation of `ErrM.pure` is `xpure`. -/
theorem errWP_pure (a : α) : errWP (ErrM.pure a) = xpure a :=
  xpredTrans_psErr_ext (errWP_apply_pure a) rfl

/-- The observation of `ErrM.seq` is `xseq` of the observations, grade included. -/
theorem errWP_seq (x : ErrM ε₁ α) (y : ErrM ε₂ β) :
    errWP (x.seq y) = xseq (errWP x) (errWP y) :=
  xpredTrans_psErr_ext (errWP_apply_seq x y) rfl

/-- The weakest precondition of `ErrM.bind` is that of `xbind` of the
observations. -/
theorem errWP_bind (x : ErrM ε₁ α) (f : α → ErrM ε₂ β) (Q : XPostCond β psErr Prop) :
    (errWP (x.bind f)).apply Q = (xbind (errWP x) fun a => errWP (f a)).apply Q :=
  errWP_apply_bind x f Q

/-- The grade of `ErrM.bind` is the sum of the grade of the head and the common
grade of the continuations. -/
theorem errWP_bind_grade_fst (x : ErrM ε₁ α) (f : α → ErrM ε₂ β) (a : α) :
    (errWP (x.bind f)).grade.1 = (errWP x).grade.1 + (errWP (f a)).grade.1 := rfl

/-- The budget rule for two sequenced programs: `xtriple_grade_le` at the
observations. -/
theorem errWP_seq_grade_le (x : ErrM ε₁ α) (y : ErrM ε₂ β) {b₁ b₂ : ℝ≥0∞}
    (h₁ : (errWP x).grade.1 ≤ b₁) (h₂ : (errWP y).grade.1 ≤ b₂) :
    (errWP (x.seq y)).grade.1 ≤ b₁ + b₂ :=
  errWP_seq x y ▸ xtriple_grade_le (errWP x) (errWP y) h₁ h₂

/-! ### Soundness against the sub-distribution -/

/-- An `XTriple` over `ErrM ε` is the support-level Hoare triple of the
sub-distribution: under `P`, every value of nonzero weight satisfies `Q`. -/
theorem errWP_triple_iff (P : Prop) (Q : α → Prop) (x : ErrM ε α) :
    XTriple (m := ErrM ε) (ps := psErr) (Ω := Prop) P x (Q, PUnit.unit)
      ↔ (P → ∀ a, x.dist (some a) ≠ 0 → Q a) :=
  Iff.rfl

/-- Soundness of a graded triple. If `XTriple P x Q` holds, the grade of the
observation of `x` is at most `b`, and `P` holds, then every value of nonzero
weight satisfies `Q`, and the sub-distribution fails with weight at most `b`. -/
theorem ErrM.sound (x : ErrM ε α) {P : Prop} {Q : α → Prop} {b : ℝ≥0∞}
    (h : XTriple (m := ErrM ε) (ps := psErr) (Ω := Prop) P x (Q, PUnit.unit))
    (hb : (XWP.xwp (ps := psErr) (Ω := Prop) x).grade.1 ≤ b) (hP : P) :
    (∀ a, x.dist (some a) ≠ 0 → Q a) ∧ x.dist none ≤ b :=
  ⟨h hP, x.fail_le.trans hb⟩

/-- The probability of the postcondition. If `XTriple P x Q` holds, the grade of
the observation of `x` is at most `b`, and `P` holds, then the total weight of
the values that satisfy `Q` is at least `1 - b`. -/
theorem ErrM.prob_post_ge (x : ErrM ε α) {P : Prop} {Q : α → Prop} {b : ℝ≥0∞}
    (h : XTriple (m := ErrM ε) (ps := psErr) (Ω := Prop) P x (Q, PUnit.unit))
    (hb : (XWP.xwp (ps := psErr) (Ω := Prop) x).grade.1 ≤ b) (hP : P) :
    1 - b ≤ ∑' a, Set.indicator {a | Q a} (fun a => x.dist (some a)) a := by
  obtain ⟨hQ, hfail⟩ := x.sound h hb hP
  have hind : ∀ a, Set.indicator {a | Q a} (fun a => x.dist (some a)) a = x.dist (some a) := by
    intro a
    by_cases ha : x.dist (some a) = 0
    · by_cases hq : Q a <;> simp [Set.indicator, hq, ha]
    · exact Set.indicator_of_mem (hQ a ha) _
  rw [tsum_congr hind, tsum_some_eq_mass, SDistr.mass]
  exact tsub_le_tsub_left hfail 1

end Observation

end CatCrypt.XDijkstra
