/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XPostShape
public import CatCryptCore.XDijkstra.Rel.XRelQ0
public import CatCryptCore.XDijkstra.XMvcgen


@[expose] public section
set_option autoImplicit false

/-!
# `XSDistrSoundness`: grounding the extended Dijkstra WP on the sub-distribution monad

This module grounds the extended-PostShape Dijkstra framework
(`XPostShape`/`XMvcgen`, `CatCrypt.XDijkstra`) directly on **`SDistr`**, CatCrypt's
crypto sub-distribution monad (`SDistr α = PMF (Option α)`, where `none` is
failure). It answers two questions with a precise boundary between them.

## Part 1 — the unary `XWP SDistr` adequacy

The **support-level unary weakest precondition** of an `SDistr` program `d` at post
`Q` asserts that `Q` holds at every point of `d`'s support:

  `(sdistrWP d).apply Q  =  ∀ a, d (some a) ≠ 0 → Q.1 a`.

(`d (some a) ≠ 0` is exactly `a ∈ SDistr.support d`; since `SDistr α = PMF (Option
α)`, a program is applied to `some a`, not `a`.) This is the natural failure-event /
support / possibilistic reading of a sub-distribution: "on every outcome that can
actually occur, `Q` holds." Its adequacy `sdistrWP_triple_iff` — mirroring
`stateWP_triple_iff` — shows that an extended `XTriple` over `SDistr` **is**
the unary support-level Hoare triple:

  `XTriple P d Q  ↔  (P → ∀ a, d (some a) ≠ 0 → Q.1 a)`.

So `xmvcgen` runs, unchanged, on the probabilistic monad for unary reasoning
(pHL / support / failure-event), reducing a triple to its residual support VC. The
two demos exercise `pure` and `bind` support conditions.

## Part 2 — the coupling as a graded `XPredTrans`, and the frontier

The RELATIONAL / probabilistic content — an `ε`-approximate coupling `liftR ε R`
(= `XRelTripleQ0`) — is presented here as a graded transformer `couplingPT ε R c c'`
at shape `.graded ℝ≥0∞ .pure`, carrying the error as its **grade** `ε`. Two facts
pin exactly how far `xmvcgen` reaches on it:

* **The grade axis fires.** `couplingPT`'s grade is `ε` (`couplingPT_grade`), and
  `xseq` threads it additively to `ε + δ` (`couplingPT_xseq_grade`), which `xmvcgen`
  computes via `xwp_graded_bind` — demonstrated in `demo_coupling_grade_fires`.
* **The coupling `apply` does NOT reduce per-operation.** `couplingPT`'s `apply` is
  the constant coupling predicate `XRelTripleQ0 ε R c c'` — an `∃`-joint-distribution
  / support condition (`RelQ0.liftR`), not a `simp`-reducible bind. Consequently the
  generic `xseq` composition is **blind** to the second coupling:
  `(xseq (couplingPT ε R c c') (couplingPT δ S d d')).apply Q = XRelTripleQ0 ε R c c'`
  (`couplingPT_xseq_apply_blind`) — it drops `δ`, `S`, and both continuations. The
  grade composes; the coupling relation does not.

The composition of couplings is `xrelQ0_seq` (`= RelQ0.liftR_bind`), the
`∃`-witness gluing `Couples_bind`/`liftRApprox_bind` — recorded here as
`couplingPT_correct_seq`, contrasting the blind `xseq.apply`.

**The frontier.** For `xmvcgen` to fire *on the coupling itself* — to reduce a
coupling `bind` compositionally the way it reduces a `pure`/`bind` support condition
in Part 1 — the framework needs a **relational coupling-spec monad** whose `bind`
*is* `Couples_bind`/`liftR_bind` (the relational Dijkstra monad of the "700
relational program logics" line: a monad over *pairs* of programs whose Kleisli
composition is the coupling composition). The product axis `xprod` (and the
`xseq` used above) is the *independent* product — a coupling only for `R = True`
(`xrelQ0_pmf_trivial`) — and is exactly what walls here. That relational spec monad
is the piece beyond the current extended-PostShape core; this module marks its
boundary.
-/

namespace CatCrypt.XDijkstra

open scoped ENNReal
open CatCrypt.Prob

/-! ## 1. The unary support-level `XWP` on `SDistr`

Mirroring `stateWP`/`stateWP_triple_iff` (`XHeapSoundness`), we observe an
`SDistr` program by its **support**: the WP at post `Q` is "`Q` holds on every point
that can occur." The natural shape is `.pure` — the support condition is a bare
`Prop`, threaded inside the observation (as `stateWP` threads the run). -/

variable {α β : Type}

/-- **The `SDistr` support-level weakest-precondition observation.** At post `Q`, the
precondition is that the success barrel `Q.1 a` holds for every `a` in the support of
`d` (`d (some a) ≠ 0`). Grade is trivial (shape `.pure` has no grade layer);
monotonicity is pointwise on the support. -/
def sdistrWP (d : SDistr α) : XPredTrans (.pure) Prop α where
  apply Q := ∀ a, d (some a) ≠ 0 → Q.1 a
  grade := PUnit.unit
  mono h := fun hQ a hs => (h.1 a) (hQ a hs)

@[simp] theorem sdistrWP_apply (d : SDistr α) (Q : XPostCond α (.pure) Prop) :
    (sdistrWP d).apply Q = ∀ a, d (some a) ≠ 0 → Q.1 a := rfl

/-- `SDistr` observed as an extended predicate transformer over `Prop`, at the pure
shape, via its support. -/
instance instXWPSDistr : XWP SDistr (.pure) Prop where
  xwp := sdistrWP

/-- The self-observation reduces to `sdistrWP` — the reduction lemma `xmvcgen` needs
to normalize the `SDistr` WP (the analogue of `xwp_self` for this instance). -/
@[simp] theorem xwp_sdistr (d : SDistr α) :
    (XWP.xwp d : XPredTrans (.pure) Prop α) = sdistrWP d := rfl

/-- **The unary `XWP SDistr` adequacy.** The extended `XTriple` over `SDistr` *is* the
unary support-level Hoare triple: `⦃P⦄ d ⦃Q⦄` holds in the framework iff `P` implies
that the success barrel `Q.1` holds at every point of `d`'s support. Definitional —
the observation was built to match the support (mirrors `stateWP_triple_iff`). -/
theorem sdistrWP_triple_iff (P : Prop) (Qf : α → Prop) (d : SDistr α) :
    XTriple (m := SDistr) (ps := .pure) (Ω := Prop) P d (Qf, PUnit.unit)
      ↔ (P → ∀ a, d (some a) ≠ 0 → Qf a) :=
  Iff.rfl

/-! ### Unary demos — `xmvcgen` fires on the probabilistic monad -/

/-- **Unary `pure` demo.** `⦃True⦄ (SDistr.pure 3) ⦃x ↦ x = 3⦄`: `xmvcgen` normalizes
the `SDistr` WP to the residual support VC `∀ a, (pure 3)(some a) ≠ 0 → a = 3`, closed
by `mem_support_pure_iff`. A unary probabilistic Hoare triple on
`SDistr`, discharged through the support adequacy. -/
theorem demo_sdistr_pure :
    XTriple (m := SDistr) (ps := .pure) (Ω := Prop)
      True (SDistr.pure (3 : Nat)) (fun x => x = 3, PUnit.unit) := by
  xmvcgen [xwp_sdistr, sdistrWP_apply]
  intro _ a ha
  exact ((SDistr.mem_support_pure_iff 3 a).mp ha).symm

/-- **Unary `bind` demo.** `⦃True⦄ (pure 1 >>= fun x => pure (x+1)) ⦃x ↦ x = 2⦄`. The
support of the bind collapses (via `pure_bind`) to `{2}`; `xmvcgen` exposes the
support VC and the bind-support fact closes it. Exercises a `bind` support condition
on the sub-distribution monad. -/
theorem demo_sdistr_bind :
    XTriple (m := SDistr) (ps := .pure) (Ω := Prop)
      True (SDistr.bind (SDistr.pure 1) (fun x => SDistr.pure (x + 1)))
      (fun x => x = 2, PUnit.unit) := by
  xmvcgen [xwp_sdistr, sdistrWP_apply]
  intro _ a ha
  rw [SDistr.pure_bind] at ha
  exact ((SDistr.mem_support_pure_iff 2 a).mp ha).symm

/-! ## 2. The coupling as a graded `XPredTrans`, and the relational frontier

`couplingPT ε R c c'` presents the `ε`-approximate coupling `XRelTripleQ0 ε R c c'`
(= `RelQ0.liftR ε R c c'`) as a graded transformer at shape `.graded ℝ≥0∞ .pure`,
carrying the coupling error as its grade `ε`. Its `apply` is the **constant** coupling
predicate — the coupling is a relation between the two programs, not a forward WP of a
postcondition, so `apply` ignores `Q`. That constancy is by design: the grade
axis threads, the coupling `apply` does not compose per-operation. -/

variable {T : Type → Type} [RelQ0 T]

/-- **The coupling predicate transformer.** Grade `ε` (the coupling error); `apply`
is the constant coupling predicate `XRelTripleQ0 ε R c c'`. Monotonicity is trivial
(the `apply` is constant in `Q`). At shape `.graded ℝ≥0∞ .pure` the assertion carrier
is `Prop`, so `apply` lands in `Prop`. -/
noncomputable def couplingPT {α β : Type} (ε : ℝ≥0∞) (R : α → β → Prop)
    (c : T α) (c' : T β) : XPredTrans (.graded ℝ≥0∞ .pure) Prop (α × β) where
  apply _ := XRelTripleQ0 ε R c c'
  grade := (ε, PUnit.unit)
  mono _ := XAssertion.le_refl (.graded ℝ≥0∞ .pure) _

/-- **The grade is the coupling error `ε`.** The grade axis of the extended framework,
read on `couplingPT`, is exactly the approximate-coupling error. -/
@[simp] theorem couplingPT_grade {α β : Type} (ε : ℝ≥0∞) (R : α → β → Prop)
    (c : T α) (c' : T β) : (couplingPT ε R c c').grade.1 = ε := rfl

/-- **The coupling `apply` is the coupling predicate, constant in `Q`.** This exposes
the frontier: `apply` is `RelQ0.liftR ε R c c'` — an `∃`-joint-distribution / support
condition — not a `simp`-reducible per-operation WP step. -/
@[simp] theorem couplingPT_apply {α β : Type} (ε : ℝ≥0∞) (R : α → β → Prop)
    (c : T α) (c' : T β) (Q : XPostCond (α × β) (.graded ℝ≥0∞ .pure) Prop) :
    (couplingPT ε R c c').apply Q = XRelTripleQ0 ε R c c' := rfl

/-! ### The grade axis fires (`xseq` threads `ε + δ`, `xmvcgen` computes it) -/

/-- **`xseq` threads the coupling grade additively to `ε + δ`.** The GRADED axis
composes couplings correctly: the sequenced head grade is the sum of the two errors —
the advantage-bound accumulation of a game hop. -/
@[simp] theorem couplingPT_xseq_grade {α β α' β' : Type}
    (ε δ : ℝ≥0∞) (R : α → β → Prop) (S : α' → β' → Prop)
    (c : T α) (c' : T β) (d : T α') (d' : T β') :
    (xseq (couplingPT ε R c c') (couplingPT δ S d d')).grade.1 = ε + δ := rfl

/-- **`xmvcgen` threads the coupling grade.** On a sequenced pair of couplings, the
budget goal `grade ≤ ε + δ` is reduced by `xmvcgen` (via `xwp_graded_bind`, unfolding
`couplingPT`) to `ε + δ ≤ ε + δ`. The grade axis of the coupling fires through the
generator unchanged. -/
theorem demo_coupling_grade_fires {α β α' β' : Type}
    (ε δ : ℝ≥0∞) (R : α → β → Prop) (S : α' → β' → Prop)
    (c : T α) (c' : T β) (d : T α') (d' : T β') :
    (xseq (couplingPT ε R c c') (couplingPT δ S d d')).grade.1 ≤ ε + δ := by
  xmvcgen [couplingPT]
  exact le_refl _

/-! ### The coupling `apply` does NOT reduce — the precise frontier

`xseq` composes the grades but is **blind** to the coupling relation: its `apply`
keeps only the first (`ε`) coupling, dropping `δ`, `S`, and both continuations. So the
generic sequencing rule of the extended core does not compose couplings; only the
grade does. -/

/-- **The `xseq` composition is blind to the second coupling.** `(xseq (couplingPT ε R
c c') (couplingPT δ S d d')).apply Q` reduces to `XRelTripleQ0 ε R c c'` — the `δ`-,
`S`-, `d`-, `d'`-data is discarded. This is the precise sense in which `xmvcgen`/`xseq`
do **not** reduce the coupling itself: the coupling `apply` composes only through the
`∃`-witness gluing of `RelQ0.liftR_bind`, not the per-operation `xseq` WP step. -/
theorem couplingPT_xseq_apply_blind {α β α' β' : Type}
    (ε δ : ℝ≥0∞) (R : α → β → Prop) (S : α' → β' → Prop)
    (c : T α) (c' : T β) (d : T α') (d' : T β')
    (Q : XPostCond (α' × β') (.graded ℝ≥0∞ .pure) Prop) :
    (xseq (couplingPT ε R c c') (couplingPT δ S d d')).apply Q
      = XRelTripleQ0 ε R c c' := rfl

/-- **The composition of couplings is `xrelQ0_seq` (= `RelQ0.liftR_bind`).**
The correct rule glues the `∃`-witnesses of the two couplings, producing a coupling of
the *bound* programs at grade `ε + δ` — the relational Dijkstra `bind` that `xseq`
cannot express. This is the operation a relational coupling-spec monad would take as
its `bind`; here it is imported from the `RelQ0` laws, sitting beyond the product-based
`xprod`/`xseq` axis of the extended core. The `couplingPT` `apply` (constant coupling
predicate, `couplingPT_apply`) is the object this rule composes. -/
theorem couplingPT_correct_seq {α β α' β' : Type}
    {ε δ : ℝ≥0∞} {R : α → β → Prop} {S : α' → β' → Prop}
    {c : T α} {c' : T β} {k₁ : α → T α'} {k₂ : β → T β'}
    (h : XRelTripleQ0 ε R c c')
    (hk : ∀ a b, R a b → XRelTripleQ0 δ S (k₁ a) (k₂ b)) :
    XRelTripleQ0 (ε + δ) S (RelQ0.bind' c k₁) (RelQ0.bind' c' k₂) :=
  xrelQ0_seq h hk

/-! ### The crypto witness: the frontier on the classical `SDistr` instance -/

/-- **The coupling transformer on the crypto monad.** `couplingPT` instantiated
at `SDistr` (with `liftR := liftRApprox`, the `ε`-approximate sub-coupling):
the grade is the coupling error, and `couplingPT_correct_seq` is the game-hop
composition `liftRApprox_bind`. The relational frontier is marked on the
cryptographic effect. -/
theorem couplingPT_sdistr_correct_seq {α β α' β' : Type}
    {ε δ : ℝ≥0∞} {R : α → β → Prop} {S : α' → β' → Prop}
    {c : SDistr α} {c' : SDistr β} {k₁ : α → SDistr α'} {k₂ : β → SDistr β'}
    (h : XRelTripleQ0 (T := SDistr) ε R c c')
    (hk : ∀ a b, R a b → XRelTripleQ0 (T := SDistr) δ S (k₁ a) (k₂ b)) :
    XRelTripleQ0 (T := SDistr) (ε + δ) S (RelQ0.bind' c k₁) (RelQ0.bind' c' k₂) :=
  couplingPT_correct_seq h hk

end CatCrypt.XDijkstra
