/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XPostShape
public import CatCryptCore.XDijkstra.XRelatorPMF
public import CatCryptCore.Relational.RelationalQ0


@[expose] public section
set_option autoImplicit false

/-!
# `XRelQ0`: the graded relational monad generalizing `XRelatorPMF`'s PMF lifting

`XRelatorPMF` gives the relational axis of the extended-PostShape Dijkstra
framework (`XPostShape.lean`) its probabilistic witness at the concrete probability monad
`PMF`: the coupling lifting `Couples μ ν R` and its sequencing rule `XRelTriplePMF_seq`.
That lifting is qualitative — a coupling either exists or it does not; there is no error
budget.

This module generalizes the concrete `PMF` to the graded relational monad `RelQ0`
(`RelationalQ0.lean`) — a probabilistic effect with a graded approximate coupling
`liftR ε R m₁ m₂` (couple `m₁`, `m₂` up to error `ε` on the support of `R`). On a `RelQ0`,
the two axes `XPostShape` keeps separate — the graded axis (a monoid grade accumulating
additively under sequencing) and the relational axis (the coupling relator `T̂`) — merge
into one object:

* the grade is the coupling error `ε`;
* `RelQ0.liftR ε R` is the `ε`-graded relational lifting `T̂`;
* the grade-additive sequencing `xseq`/`xrel_seq` and the coupling composition
  `liftR_bind` are the same rule — the sequenced grade `ε + δ` is at once the additive
  grade and the composed coupling error;
* the `grade ≤ budget` verification condition is the coupling-error / advantage bound
  `ε ≤ budget`.

The instance `SDistr` (the crypto sub-distribution monad) runs this graded relational axis
on the cryptographic effect; `PMF` is a `RelQ0` instance with `liftR := Couples` (the
`ε`-collapsed, qualitative fragment), the `0`-graded special case of the generalization.

## Principal declarations

* `XRelTripleQ0 ε R m₁ m₂ := RelQ0.liftR ε R m₁ m₂` — the graded relational triple over any
  `RelQ0`, and `xrelQ0_seq` (grade-additive `ε + δ` sequencing, delegating to
  `RelQ0.liftR_bind`): the fused graded+relational sequencing rule.
* `grade_is_coupling_error` / `budget_vc_is_eps_bound` — with the grade `G := ℝ≥0∞`, the
  `xseq` head grade is `ε + δ` (`xwp_graded_bind`) and the budget VC `grade ≤ budget` is
  the advantage bound `ε ≤ budget` (`xtriple_grade_le`): the grade axis is the coupling
  error.
* `instRelQ0PMF` — `PMF` as a `RelQ0` with `liftR ε R := Couples · · R` (ignoring `ε`),
  exhibiting `XRelatorPMF`'s `Couples`/`Couples_bind`/`Couples_pure` as the `RelQ0` laws at the
  `ε`-collapsed (`liftR 0`) instance; `Couples_mono_rel` supplies the
  relation-monotonicity law.
* `sdistr_graded_relational_seq` — the graded relational sequencing rule at the crypto
  instance `SDistr`.
-/

namespace CatCrypt.XDijkstra

open scoped ENNReal
open CatCrypt.Prob

/-! ## 1. The graded relational triple over a `RelQ0` monad

`XRelTripleQ0 ε R m₁ m₂` is the probabilistic relational Hoare judgment at
grade/error `ε`: `m₁` and `m₂` are `ε`-approximately coupled on the support of
`R`. It is `RelQ0.liftR`, and its sequencing rule is the `xrel_seq`/`xseq`
analogue whose grade adds. -/

/-- **The graded relational triple over a `RelQ0`.** `m₁`, `m₂` are coupled up to
error `ε` on the support of `R` — the `ε`-graded relational lifting `T̂`, at `PMF`
the qualitative `XRelatorPMF` coupling. -/
def XRelTripleQ0 {T : Type → Type} [RelQ0 T] {α β : Type}
    (ε : ℝ≥0∞) (R : α → β → Prop) (m₁ : T α) (m₂ : T β) : Prop :=
  RelQ0.liftR ε R m₁ m₂

/-- **Coupling `return`.** `R`-related points lift to the zero-error triple — the
`RelQ0` `liftR_pure` law, the graded generalization of `Couples_pure`. -/
theorem xrelQ0_pure {T : Type → Type} [RelQ0 T] {α β : Type}
    {a : α} {b : β} {R : α → β → Prop} (h : R a b) :
    XRelTripleQ0 (T := T) 0 R (RelQ0.pure' a) (RelQ0.pure' b) :=
  RelQ0.liftR_pure h

/-- **The fused graded relational sequencing rule.** From an `ε`-triple on the
prefixes and, at every `R`-related pair, a `δ`-triple on the continuations,
obtain a triple on the sequenced programs at grade `ε + δ`. Delegates to
`RelQ0.liftR_bind`. The output grade `ε + δ` is at once the grade-additive `xseq`
(cost/error accumulation) and the pRHL coupling composition. -/
theorem xrelQ0_seq {T : Type → Type} [RelQ0 T] {α β α' β' : Type}
    {ε δ : ℝ≥0∞} {R : α → β → Prop} {S : α' → β' → Prop}
    {m₁ : T α} {m₂ : T β} {k₁ : α → T α'} {k₂ : β → T β'}
    (h : XRelTripleQ0 ε R m₁ m₂)
    (hk : ∀ a b, R a b → XRelTripleQ0 δ S (k₁ a) (k₂ b)) :
    XRelTripleQ0 (ε + δ) S (RelQ0.bind' m₁ k₁) (RelQ0.bind' m₂ k₂) :=
  RelQ0.liftR_bind h hk

/-- **Grade monotonicity of the triple.** A larger error budget still holds. -/
theorem xrelQ0_mono_eps {T : Type → Type} [RelQ0 T] {α β : Type}
    {ε ε' : ℝ≥0∞} {R : α → β → Prop} {m₁ : T α} {m₂ : T β}
    (hε : ε ≤ ε') (h : XRelTripleQ0 ε R m₁ m₂) : XRelTripleQ0 ε' R m₁ m₂ :=
  RelQ0.liftR_mono_eps hε h

/-- **Relation weakening of the triple.** A coupling on `R` is a coupling on any
weaker `S ⊇ R`, at the same grade. -/
theorem xrelQ0_mono_rel {T : Type → Type} [RelQ0 T] {α β : Type}
    {ε : ℝ≥0∞} {R S : α → β → Prop} {m₁ : T α} {m₂ : T β}
    (hRS : ∀ a b, R a b → S a b) (h : XRelTripleQ0 ε R m₁ m₂) :
    XRelTripleQ0 ε S m₁ m₂ :=
  RelQ0.liftR_mono_rel hRS h

/-! ## 2. Grade axis = coupling error `ε`

Instantiate the XDijkstra grade with `G := ℝ≥0∞` (a valid grade: an
`OrderedAddCommMonoid`). At shape `.graded ℝ≥0∞ .pure`, the head grade of a
transformer is an element of `ℝ≥0∞` — a coupling error. The additive `xseq` grade
`x.grade.1 + y.grade.1` (`xwp_graded_bind`) is then exactly the `ε + δ` of
`xrelQ0_seq`, and the budget VC `grade ≤ budget` is the advantage bound
`ε ≤ budget` (`xtriple_grade_le`). -/

section GradeIsEps

variable {Ω : Type} [Preorder Ω] {α β : Type}

/-- **The sequenced grade is the composed coupling error `ε + δ`.** With head
grades `ε`, `δ` on two transformers at the `ℝ≥0∞`-grade shape, `xseq`'s head grade
is `ε + δ`, the quantity `xrelQ0_seq` reports. So the grade-value and the `RelQ0`
coupling error are the same object. -/
theorem grade_is_coupling_error
    (x : XPredTrans (.graded ℝ≥0∞ .pure) Ω α)
    (y : XPredTrans (.graded ℝ≥0∞ .pure) Ω β)
    {ε δ : ℝ≥0∞} (hx : x.grade.1 = ε) (hy : y.grade.1 = δ) :
    (xseq x y).grade.1 = ε + δ := by
  rw [xwp_graded_bind, hx, hy]

/-- **The grade-VC is the advantage bound.** If two sequenced steps each stay
within a sub-error `b₁`, `b₂`, their composition stays within `b₁ + b₂`. This is
`xtriple_grade_le` at `G := ℝ≥0∞`: the `grade ≤ budget` verification condition,
read on the coupling error, is the advantage bound. -/
theorem budget_vc_is_eps_bound
    (x : XPredTrans (.graded ℝ≥0∞ .pure) Ω α)
    (y : XPredTrans (.graded ℝ≥0∞ .pure) Ω β)
    {b₁ b₂ : ℝ≥0∞} (h₁ : x.grade.1 ≤ b₁) (h₂ : y.grade.1 ≤ b₂) :
    (xseq x y).grade.1 ≤ b₁ + b₂ :=
  xtriple_grade_le x y h₁ h₂

end GradeIsEps

/-! ## 3. `RelQ0` generalizes the `XRelatorPMF` PMF prototype

`XRelatorPMF`'s `Couples μ ν R` is a qualitative coupling — no error grade. It is the `RelQ0`
lifting at its `ε`-collapsed instance: the `PMF` lifting `liftR ε R := Couples · · R`
(ignoring `ε`, since an exact coupling is a zero-error one), and `XRelatorPMF`'s
`Couples_pure`/`Couples_bind` are the `RelQ0` `liftR_pure`/`liftR_bind` laws — grade-additive
bind included, the grade carried vacuously. The relation-monotonicity law is
`Couples_mono_rel`. -/

variable {α β : Type}

/-- **Relation weakening of a `PMF` coupling.** A coupling supported on `R` is a
coupling supported on any weaker `S ⊇ R`: the same witness `κ`, support upgraded.
This is the `liftR_mono_rel` law. -/
theorem Couples_mono_rel {R S : α → β → Prop} {μ : PMF α} {ν : PMF β}
    (hRS : ∀ a b, R a b → S a b) (h : Couples μ ν R) : Couples μ ν S := by
  obtain ⟨κ, hκ⟩ := h
  exact ⟨κ, hκ.marg_fst, hκ.marg_snd, fun p hp => hRS p.1 p.2 (hκ.supp p hp)⟩

/-- **`PMF` as a graded relational `RelQ0` monad.** The lifting `liftR ε R` is the `XRelatorPMF`
coupling `Couples · · R`, independent of `ε` (an exact coupling is a zero-error one). Its
four laws are `Couples_pure`, `Couples_bind`, `Couples_mono_rel`, and grade weakening. This
exhibits the qualitative prototype as the `ε`-collapsed instance of the graded relational
monad. -/
noncomputable instance instRelQ0PMF : RelQ0 PMF where
  pure' := PMF.pure
  bind' := PMF.bind
  liftR := fun _ε R μ ν => Couples μ ν R
  liftR_pure h := Couples_pure h
  liftR_bind h hf := Couples_bind h hf
  liftR_mono_rel hRS h := Couples_mono_rel hRS h
  liftR_mono_eps _ h := h

/-- **The `PMF` lifting is `XRelatorPMF`'s `Couples`**, at every grade: the graded
relator collapses to the qualitative one. -/
theorem pmf_liftR_eq_couples {ε : ℝ≥0∞} {R : α → β → Prop} {μ : PMF α} {ν : PMF β} :
    (RelQ0.liftR (T := PMF) ε R μ ν) = Couples μ ν R := rfl

/-- **`XRelatorPMF`'s `Couples` is the `0`-graded triple.** The qualitative `XRelatorPMF`
coupling is `XRelTripleQ0` at error `0` — the sense in which `RelQ0` is the
`ε`-graded generalization of the PMF prototype. -/
theorem couples_iff_xrelQ0_zero {R : α → β → Prop} {μ : PMF α} {ν : PMF β} :
    Couples μ ν R ↔ XRelTripleQ0 (T := PMF) 0 R μ ν := Iff.rfl

/-- **The deterministic product is the trivial (`R = True`) triple.** `XPostShape`'s
independent product `xprod` — a coupling only for `fun _ _ => True` — is the
`R = True` case of the relational triple, at any grade. -/
theorem xrelQ0_pmf_trivial (ε : ℝ≥0∞) (μ : PMF α) (ν : PMF β) :
    XRelTripleQ0 (T := PMF) ε (fun _ _ => True) μ ν :=
  Couples_indep μ ν

/-! ## 4. The instance `SDistr`

`RelationalQ0.lean` supplies `instRelQ0SDistr`, the `RelQ0` instance on `SDistr` (the
crypto sub-distribution monad) with `liftR := liftRApprox` (the `ε`-approximate
sub-coupling). The graded relational axis above runs on the cryptographic effect. This
section records the sequencing rule specialized there. -/

/-- The graded relational axis lives on the crypto monad `SDistr`. -/
noncomputable example : RelQ0 SDistr := inferInstance

/-- **Graded relational sequencing on `SDistr`.** `xrelQ0_seq` at the crypto instance: two
`ε`- and `δ`-approximately coupled steps compose to an `(ε + δ)`-coupled sequence. The
error/grade addition is the advantage-bound accumulation of a game hop on the
sub-distribution monad. -/
theorem sdistr_graded_relational_seq {α β α' β' : Type}
    {ε δ : ℝ≥0∞} {R : α → β → Prop} {S : α' → β' → Prop}
    {m₁ : SDistr α} {m₂ : SDistr β} {k₁ : α → SDistr α'} {k₂ : β → SDistr β'}
    (h : XRelTripleQ0 (T := SDistr) ε R m₁ m₂)
    (hk : ∀ a b, R a b → XRelTripleQ0 (T := SDistr) δ S (k₁ a) (k₂ b)) :
    XRelTripleQ0 (T := SDistr) (ε + δ) S (RelQ0.bind' m₁ k₁) (RelQ0.bind' m₂ k₂) :=
  xrelQ0_seq h hk

end CatCrypt.XDijkstra
