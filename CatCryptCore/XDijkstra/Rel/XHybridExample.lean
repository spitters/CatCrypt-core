/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.Rel.XRelQ0
public import CatCryptCore.XDijkstra.XMvcgenControl


@[expose] public section
set_option autoImplicit false

/-!
# `XHybridExample`: the XDijkstra framework on a cryptographic reduction pattern

A hybrid argument run over the sub-distribution monad `SDistr` (`instRelQ0SDistr`),
applying the extended-PostShape (XDijkstra) framework. The division of labour in a
reduction:

* the **per-hop couplings are leaves** — hypotheses, as in a reduction where each
  hybrid step's advantage is a primitive-security assumption
  (`XRelTripleQ0 εᵢ Eq Gᵢ Gᵢ₊₁`);
* the **ε-summation and frame bookkeeping around the couplings** is mechanized by the
  grade axis. The grade is the coupling error (`grade_is_coupling_error`), so the
  grade-additive sequencing of `XPostShape` (`xseq` / `xwp_graded_bind`, driven by
  `xmvcgen`, and the loop fold `xfor`/`xfor_grade_fst`) computes `Σ εᵢ`, leaving only
  the leaves to hand.

## Two composition modes, both grade-additive

A hybrid composes couplings **horizontally** (transitivity along a chain of games on
the same type, at equality post — game hopping): `liftRApprox_trans_eq` chains
`ε₁`- and `ε₂`-couplings into an `(ε₁ + ε₂)`-coupling. This is the composition the
grade axis mechanizes here. The **vertical** mode — Kleisli/bind sequencing of
sub-programs — is `xrelQ0_seq` (`RelQ0.liftR_bind`), also grade-additive
(`hybrid_bind_seq`). Both add the error/grade.

## Principal declarations

1. `hybrid3_bound` — a 3-hop hybrid `G0 ⤳ G1 ⤳ G2 ⤳ G3` over `SDistr`, from the three
   coupling leaves to the composed `XRelTripleQ0 (ε₁+ε₂+ε₃) Eq G0 G3`.
2. `hybrid3_grade` / `hybrid3_budget` — the summation `ε₁+ε₂+ε₃` produced by
   `xmvcgen` threading the grade through an `xseq`-chain of hop transformers at the
   `.graded ℝ≥0∞ .pure` shape, and the residual advantage bound `ε₁+ε₂+ε₃ ≤ budget`.
   `hybrid3_fused` bridges them: the grade `xmvcgen` threads is the coupling error, and
   the budget VC weakens the coupling (`xrelQ0_mono_eps`).
3. `hybridN_bound` — a general-`n` uniform-hop hybrid composed to `n • ε` **by
   induction, no unrolling**, with the loop grade computed by `xforR`/`xforR_grade_fst`
   (the `ℝ≥0∞`-graded mirror of `XMvcgenControl`'s `xfor`/`xfor_grade_fst`) and the
   residual `n • ε ≤ budget`; `hybridN_fused` bridges coupling and grade as above.

## Coupling and graded transformer as separate objects

`xmvcgen` normalizes `XPredTrans`/`XPT`/`XRelTriple` goals; `XRelTripleQ0`
(`= RelQ0.liftR`) is a `Prop` about `SDistr`, not an `XPredTrans`. A direct
`xmvcgen`-over-`liftR` reduction would need `RelQ0.liftR` presented as an
`XPredTrans (.graded ℝ≥0∞ .pure)`-shaped observation of `SDistr` (an
`XWP SDistr (.graded ℝ≥0∞ .pure) Ω` whose `apply` is the coupling predicate and whose
grade is the error). The framework instead keeps the coupling (`liftR`) and the graded
transformer (`XPredTrans`) as separate objects **joined by the shared `ℝ≥0∞` grade**:
the composition here goes through the chain lemma (`liftRApprox_trans_eq`), the
`xseq`/`xforR` grade (on which `xmvcgen` fires), and the budget residual, bridged by
`xrelQ0_mono_eps`.
-/

namespace CatCrypt.XDijkstra

open scoped ENNReal
open CatCrypt CatCrypt.Prob

variable {α β α' β' : Type}

/-! ## 0. Coupling reflexivity and transitivity on `SDistr` at equality

The hybrid chains couplings on games of the same type at the equality relation
(game-hopping post). Transitivity of the `ε`-coupling is `liftRApprox_trans_eq`; the
`n = 0` base of the general-`n` chain needs reflexivity, which the min-diagonal witness
supplies (`tvMargin d d = 0`). Both are restated at the `XRelTripleQ0` level, which on
`SDistr` is definitionally `liftRApprox` (`instRelQ0SDistr`). -/

/-- One-sided statistical distance of a distribution from itself is `0`. -/
theorem tvMargin_self (d : SDistr α) : tvMargin d d = 0 := by
  simp only [tvMargin, tsub_self, tsum_zero]

/-- **Reflexivity of the equality coupling at grade `0`.** A distribution is
`0`-coupled to itself at `Eq` (the min-diagonal sub-coupling). -/
theorem liftRApprox_refl_eq (d : SDistr α) : liftRApprox 0 Eq d d :=
  liftRApprox_eq_of_tv (le_of_eq (tvMargin_self d)) (le_of_eq (tvMargin_self d))

/-- **The `0`-grade reflexive triple** on `SDistr`: `XRelTripleQ0 0 Eq d d`. -/
theorem xrelQ0_refl_eq (d : SDistr α) : XRelTripleQ0 (T := SDistr) 0 Eq d d :=
  liftRApprox_refl_eq d

/-- **Coupling transitivity (game hopping).** `ε₁`- and `ε₂`-couplings at `Eq` on a
chain `d₁ ⤳ d₂ ⤳ d₃` compose to an `(ε₁ + ε₂)`-coupling `d₁ ⤳ d₃` — the horizontal,
grade-additive composition a hybrid argument is built from. Delegates to
`liftRApprox_trans_eq`. -/
theorem xrelQ0_trans_eq {d₁ d₂ d₃ : SDistr α} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : XRelTripleQ0 (T := SDistr) ε₁ Eq d₁ d₂)
    (h₂ : XRelTripleQ0 (T := SDistr) ε₂ Eq d₂ d₃) :
    XRelTripleQ0 (T := SDistr) (ε₁ + ε₂) Eq d₁ d₃ :=
  liftRApprox_trans_eq h₁ h₂

/-! ## 1. A 3-hop hybrid over `SDistr` — the leaves are couplings, composition is summed

Games `G0 G1 G2 G3 : SDistr α` are abstract (opaque distributions). The three per-hop
couplings `h₁ h₂ h₃` are **hypotheses** — the leaves, standing for the primitive
advantages of a reduction. Composing them into the end-to-end `G0 ⤳ G3` coupling
sums the advantages: `ε₁ + ε₂ + ε₃`. -/

/-- **The 3-hop hybrid bound.** From the three coupling leaves obtain the composed
coupling at the summed advantage `ε₁ + ε₂ + ε₃`. The advantage summation is
mechanized; the three leaves are the only hand-provided facts. -/
theorem hybrid3_bound (G0 G1 G2 G3 : SDistr α) {ε₁ ε₂ ε₃ : ℝ≥0∞}
    (h₁ : XRelTripleQ0 (T := SDistr) ε₁ Eq G0 G1)
    (h₂ : XRelTripleQ0 (T := SDistr) ε₂ Eq G1 G2)
    (h₃ : XRelTripleQ0 (T := SDistr) ε₃ Eq G2 G3) :
    XRelTripleQ0 (T := SDistr) (ε₁ + ε₂ + ε₃) Eq G0 G3 :=
  xrelQ0_trans_eq (xrelQ0_trans_eq h₁ h₂) h₃

/-- **Vertical (Kleisli) composition, also grade-additive.** The dual composition mode:
a coupling of prefixes and pointwise couplings of continuations sequence to a coupling
of the binds, at grade `ε + δ`. This is `xrelQ0_seq` (`RelQ0.liftR_bind`) on `SDistr`
— the sequential-game-step form; `hybrid3_bound` above is the horizontal
game-hop form. Both add the error/grade. -/
theorem hybrid_bind_seq {ε δ : ℝ≥0∞} {R : α → β → Prop} {S : α' → β' → Prop}
    {m₁ : SDistr α} {m₂ : SDistr β} {k₁ : α → SDistr α'} {k₂ : β → SDistr β'}
    (h : XRelTripleQ0 (T := SDistr) ε R m₁ m₂)
    (hk : ∀ a b, R a b → XRelTripleQ0 (T := SDistr) δ S (k₁ a) (k₂ b)) :
    XRelTripleQ0 (T := SDistr) (ε + δ) S (RelQ0.bind' m₁ k₁) (RelQ0.bind' m₂ k₂) :=
  xrelQ0_seq h hk

/-! ## 2. `xmvcgen` mechanizes the ε-summation

The grade axis (`XPostShape`) carries the coupling error as a value grade at shape
`.graded ℝ≥0∞ .pure`. A **hop transformer** `hop ε` has head grade `ε`; sequencing three
via `xseq` and threading the grade with `xmvcgen` computes the total advantage
`ε₁ + ε₂ + ε₃`, and the `grade ≤ budget` VC is the advantage bound. This is the
bookkeeping the tactic automates — the leaves (`h₁/h₂/h₃`) stay hand-provided. -/

/-- A hop transformer at shape `.graded ℝ≥0∞ .pure`, head grade the hop advantage `e`. -/
def hop (e : ℝ≥0∞) : XPredTrans (.graded ℝ≥0∞ .pure) Prop Unit where
  apply Q := Q.1 ()
  grade := (e, ⟨⟩)
  mono h := h.1 ()

@[simp] theorem hop_grade_fst (e : ℝ≥0∞) : (hop e).grade.1 = e := rfl

@[simp] theorem hop_apply (e : ℝ≥0∞) (Q : XPostCond Unit (.graded ℝ≥0∞ .pure) Prop) :
    (hop e).apply Q = Q.1 () := rfl

/-- **`xmvcgen` threads the summed advantage.** The head grade of the `xseq`-chain of
three hop transformers reduces — via `xwp_graded_bind`, applied by `xmvcgen` — to the
sum `ε₁ + ε₂ + ε₃`. No manual grade bookkeeping. -/
theorem hybrid3_grade (e₁ e₂ e₃ : ℝ≥0∞) :
    (xseq (xseq (hop e₁) (hop e₂)) (hop e₃)).grade.1 = e₁ + e₂ + e₃ := by
  xmvcgen [hop_grade_fst]

/-- **The budget VC is the advantage bound.** `xmvcgen` threads the chain grade to the
sum and leaves the residual `ε₁ + ε₂ + ε₃ ≤ budget` — the advantage bound, closed
against the budget hypothesis. -/
theorem hybrid3_budget (e₁ e₂ e₃ budget : ℝ≥0∞) (h : e₁ + e₂ + e₃ ≤ budget) :
    (xseq (xseq (hop e₁) (hop e₂)) (hop e₃)).grade.1 ≤ budget := by
  xmvcgen [hop_grade_fst]
  exact h

/-- **Fused: the threaded grade is the coupling error.** From the three coupling leaves
and a budget VC on the `xseq`-chain grade (the quantity `xmvcgen` threads), obtain the
end-to-end coupling at the budget. The composition layer
(`hybrid3_grade` + `xrelQ0_mono_eps`) is mechanized; the leaves are the only hand work. -/
theorem hybrid3_fused (G0 G1 G2 G3 : SDistr α) (e₁ e₂ e₃ budget : ℝ≥0∞)
    (h₁ : XRelTripleQ0 (T := SDistr) e₁ Eq G0 G1)
    (h₂ : XRelTripleQ0 (T := SDistr) e₂ Eq G1 G2)
    (h₃ : XRelTripleQ0 (T := SDistr) e₃ Eq G2 G3)
    (hbudget : (xseq (xseq (hop e₁) (hop e₂)) (hop e₃)).grade.1 ≤ budget) :
    XRelTripleQ0 (T := SDistr) budget Eq G0 G3 := by
  have hcoup : XRelTripleQ0 (T := SDistr) (e₁ + e₂ + e₃) Eq G0 G3 :=
    hybrid3_bound G0 G1 G2 G3 h₁ h₂ h₃
  have hgrade : (xseq (xseq (hop e₁) (hop e₂)) (hop e₃)).grade.1 = e₁ + e₂ + e₃ :=
    hybrid3_grade e₁ e₂ e₃
  exact xrelQ0_mono_eps (hgrade ▸ hbudget) hcoup

/-! ## 3. General-`n` hybrid

A uniform-hop hybrid: `n` hops, each at advantage `ε`, over a sequence of games
`Gseq : ℕ → SDistr α`. The coupling composes to `n • ε` **by induction — general `n`, no
unrolling** — using reflexivity at the base and transitivity at the step. The loop grade
is computed by `xforR`/`xforR_grade_fst`, the `ℝ≥0∞`-graded mirror of `XMvcgenControl`'s
`xfor`/`xfor_grade_fst`, whose head grade is `n • body.grade.1` by induction — the
`n·ε` scaling bookkeeping, which is impractical to unroll by hand. -/

/-- The `ℝ≥0∞`-graded counted loop: fold `body` `n` times through `xseq`. Mirror of
`XMvcgenControl.xfor` at the `ℝ≥0∞` grade a coupling error lives in. -/
def xforR (n : ℕ) (body : XPredTrans (.graded ℝ≥0∞ .pure) Prop Unit) :
    XPredTrans (.graded ℝ≥0∞ .pure) Prop Unit :=
  match n with
  | 0 => xpure ()
  | n + 1 => xseq body (xforR n body)

/-- **The loop grade is `n • body.grade.1`.** Proved by induction on `n`; the general
`n` closes with no unrolling, threading one `body.grade.1` per iteration through `xseq`.
The `ℝ≥0∞` analogue of `xfor_grade_fst`. -/
theorem xforR_grade_fst (n : ℕ) (body : XPredTrans (.graded ℝ≥0∞ .pure) Prop Unit) :
    (xforR n body).grade.1 = n • body.grade.1 := by
  induction n with
  | zero =>
    show (xforR 0 body).grade.1 = (0 : ℕ) • body.grade.1
    rw [zero_nsmul]
    rfl
  | succ k ih =>
    show (xseq body (xforR k body)).grade.1 = (k + 1) • body.grade.1
    rw [xwp_graded_bind, ih, succ_nsmul]
    exact add_comm _ _

/-- **The general-`n` uniform-hop hybrid bound.** With a uniform per-hop coupling `ε`
along `Gseq`, the composed coupling `Gseq 0 ⤳ Gseq n` holds at total advantage `n • ε`.
By induction: reflexivity (`xrelQ0_refl_eq`) at `n = 0`, transitivity
(`xrelQ0_trans_eq`) at the step — no unrolling. -/
theorem hybridN_bound (Gseq : ℕ → SDistr α) (ε : ℝ≥0∞)
    (hstep : ∀ i, XRelTripleQ0 (T := SDistr) ε Eq (Gseq i) (Gseq (i + 1))) (n : ℕ) :
    XRelTripleQ0 (T := SDistr) (n • ε) Eq (Gseq 0) (Gseq n) := by
  induction n with
  | zero =>
    rw [zero_nsmul]
    exact xrelQ0_refl_eq (Gseq 0)
  | succ k ih =>
    rw [succ_nsmul]
    exact xrelQ0_trans_eq ih (hstep k)

/-- **The general-`n` budget VC is `n • ε ≤ budget`.** `xforR_grade_fst` reduces the
loop grade to `n • ε` for general `n`, leaving the residual advantage bound. -/
theorem hybridN_budget (ε budget : ℝ≥0∞) (n : ℕ) (h : n • ε ≤ budget) :
    (xforR n (hop ε)).grade.1 ≤ budget := by
  rw [xforR_grade_fst, hop_grade_fst]
  exact h

/-- **Fused general-`n`: the loop grade is the total coupling error.** From the uniform
hop hypothesis and a budget VC on the `xforR` grade `n • ε` (threaded by
`xforR_grade_fst`), obtain the end-to-end `n`-hybrid coupling at the budget. The `n·ε`
scaling bookkeeping is mechanized; the per-hop coupling is the leaf. -/
theorem hybridN_fused (Gseq : ℕ → SDistr α) (ε budget : ℝ≥0∞) (n : ℕ)
    (hstep : ∀ i, XRelTripleQ0 (T := SDistr) ε Eq (Gseq i) (Gseq (i + 1)))
    (hbudget : (xforR n (hop ε)).grade.1 ≤ budget) :
    XRelTripleQ0 (T := SDistr) budget Eq (Gseq 0) (Gseq n) := by
  refine xrelQ0_mono_eps ?_ (hybridN_bound Gseq ε hstep n)
  rw [xforR_grade_fst, hop_grade_fst] at hbudget
  exact hbudget

/-- **The `ℕ`-graded loop mechanism via `xfor`.** The unit-hop instance run through
`xfor`/`xfor_grade_fst`: `n` unit-cost hops have grade `n`, residual `n ≤ budget`, for
general `n`. This is the loop grade combinator `xforR_grade_fst` mirrors at `ℝ≥0∞`. -/
theorem hybridN_unit_budget (n budget : ℕ) (h : n ≤ budget) :
    (xfor n (tick 1)).grade.1 ≤ budget := by
  rw [xfor_grade_fst, tick_grade_fst, Nat.mul_one]
  exact h

end CatCrypt.XDijkstra
