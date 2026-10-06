/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.TypeStar
public import Mathlib.Data.Nat.Notation
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Defs.PartialOrder

@[expose] public section

set_option autoImplicit false

/-!
# A graded weakest-precondition (graded Dijkstra monad) prototype

`Std.Do`/`mvcgen`, the weakest-precondition metatheory, is built on a **fixed** effect stack
`Std.Do.PostShape` (`pure | arg σ | except ε`). There is no place in that stack
for a *grade*: an index drawn from a monoid that **accumulates under sequencing**
and is not, in general, state-encodable. Two motivating grades:

* the `ε` / **error budget** of the enriched (metric) setting — the total
  advantage a composed reduction may spend, which *adds* as steps compose;
* **interface accumulation** in general — the resources/oracles a computation
  touches, again accumulated monoidally along a bind chain.

This module builds the graded predicate transformer **standalone** (it does not
touch `Std.Do`), proves the graded Hoare algebra (consequence with a *grade-may-
only-increase* side, and grade-**additive** sequencing), demonstrates it on a
concrete two-step cost-`2` computation, and states precisely what `mvcgen`
integration would require.

## The construction

`GPredTrans g α` is a **monotone** predicate transformer `(α → Prop) → Prop`
carrying a *grade index* `g : G`, `G` an ordered additive monoid. The grade is a
type-level index: it is tracked in the type of every transformer, produced by
`gpure` at `0` and by `gbind` at `g₁ + g₂` — the monoid multiplication. (The
underlying transformer does not read the grade; graded monads standardly index a
uniform carrier. Monotonicity is bundled because WP post-weakening and
sequencing require it — a bare `(α → Prop) → Prop` is not monotone, so the
Hoare rules would be unprovable without it. This is the "cleanest equivalent
carrying the grade".)

* `gpure : α → GPredTrans 0 α`
* `gbind : GPredTrans g₁ α → (α → GPredTrans g₂ β) → GPredTrans (g₁ + g₂) β`
* `GTriple g P t Q := P → t.wp Q` — the WP triple with a `Prop` precondition.

The graded Hoare algebra:

* `consequence` — weaken the precondition, weaken the postcondition (uses the
  bundled monotonicity), and the grade may only **increase** (`g ≤ g'`, via
  `gweaken`);
* `seq` — `GTriple g₁ P t₁ (fun _ => R) → GTriple g₂ R t₂ Q →
  GTriple (g₁ + g₂) P (t₁ >>= fun _ => t₂) Q`: the classic Hoare composition,
  and the grades **add**. This is the graded content — cost/budget composes.

`demo_two_steps` sequences two unit-cost steps (`G := ℕ`) into a triple at grade
`1 + 1 = 2`, and `demo_wp` shows the postcondition threading through both steps.

## Why this does NOT plug into `mvcgen` today (the tier-3 framework gap)

`Std.Do.PostShape` is a fixed inductive `pure | arg σ | except ε` with **no
monoid index**, and `mvcgen`'s verification-condition generator threads a
`PredTrans ps` over exactly that stack: its `@[spec]` `bind` rule composes
transformers, but there is **no slot in which a grade `g` could accumulate to
`g₁ + g₂`** as `gbind` does here. Two ways one might try to bridge it, and why
each is insufficient:

1. **Encode the grade as `.arg G` reader/writer state.** This only works when
   the grade is *state-encodable*: the computation must literally read/write a
   `G`-valued cell (`modify (· + cost)`), which changes the operational
   semantics (it adds a real state component) and forces the program to
   manipulate `G`. The enriched-setting error budget is a *proof-level* index on
   the transformer, not a runtime value the code carries — so this route
   mis-models it.

2. **Add a monoid-graded `PostShape` (or a grade parameter on `PredTrans`).**
   This is the faithful route: `PostShape` (or the transformer) would gain a
   grade index `g : G` with a `Triple`/`bind` `@[spec]` lemma whose conclusion
   grade is `g₁ + g₂` — exactly `gbind`/`seq` here, lifted into the `Std.Do`
   metatheory so `mvcgen` accumulates the grade while it walks the VC. `Std.Do`
   has no such constructor; adding it (and teaching `mvcgen`'s spec engine to
   thread the monoid) is the tier-3 framework extension this prototype scopes.

The graded algebra below is proved standalone, outside `mvcgen`: the missing
piece is a grade index on `PostShape`/`PredTrans` plus a grade-additive `bind`
spec.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent.GradedWP

/-! ## 1. The grade-indexed monotone predicate transformer

`G` is a general ordered additive monoid (`[AddCommMonoid G] [Preorder G]`): the
grade needs `0` (for `gpure`), `+` (for `gbind`), and `≤` (for the grade-increase
direction of `consequence`). Both `ℕ` (cost) and `ℝ≥0∞` (budget) are instances;
the demos use `ℕ`. -/

variable {G : Type*} [AddCommMonoid G] [Preorder G]

/-- A **graded, monotone predicate transformer**: a WP transformer
`(α → Prop) → Prop` carrying a grade index `g : G`. Monotonicity (`mono`) is
bundled because WP post-weakening and sequencing require it. The grade `g` is a
type-level index — it is not a field, so it is tracked in the type of every
transformer without altering the underlying computation. -/
structure GPredTrans (g : G) (α : Type) where
  /-- The underlying weakest-precondition transformer. -/
  wp : (α → Prop) → Prop
  /-- The transformer is monotone in its postcondition. -/
  mono : ∀ {Q Q' : α → Prop}, (∀ a, Q a → Q' a) → wp Q → wp Q'

/-- **Graded return.** Grade `0`: `wp Q := Q a`, trivially monotone. -/
def gpure {α : Type} (a : α) : GPredTrans (0 : G) α where
  wp Q := Q a
  mono h hQ := h a hQ

/-- **Graded bind.** Grades **add**: sequencing a `g₁`-transformer with a
`g₂`-continuation yields a `g₁ + g₂`-transformer. The WP is the standard
continuation-monad composition; monotonicity is inherited from both stages. -/
def gbind {α β : Type} {g₁ g₂ : G}
    (t : GPredTrans g₁ α) (f : α → GPredTrans g₂ β) : GPredTrans (g₁ + g₂) β where
  wp Q := t.wp (fun a => (f a).wp Q)
  mono h hQ := t.mono (fun a hfa => (f a).mono h hfa) hQ

/-- **The graded WP triple.** With a `Prop` precondition `P`: if `P` holds, the
weakest precondition of `t` at post `Q` holds. -/
def GTriple {α : Type} (g : G) (P : Prop) (t : GPredTrans g α) (Q : α → Prop) : Prop :=
  P → t.wp Q

/-- **Grade weakening.** Reindex a transformer to a larger grade (`g ≤ g'`). The
underlying monotone transformer is unchanged — only the grade index grows; the
`g ≤ g'` hypothesis records the *direction* (grades may only increase). -/
def gweaken {α : Type} {g g' : G} (_hg : g ≤ g') (t : GPredTrans g α) : GPredTrans g' α where
  wp := t.wp
  mono := t.mono

/-! ## 2. The graded Hoare algebra -/

omit [AddCommMonoid G] in
/-- **Consequence.** Weaken the precondition (`P' → P`), weaken the postcondition
(`∀ a, Q a → Q' a`, discharged by the bundled monotonicity), and let the grade
**increase** (`g ≤ g'`, via `gweaken`). -/
theorem consequence {α : Type} {g g' : G} {P P' : Prop} {t : GPredTrans g α}
    {Q Q' : α → Prop}
    (hg : g ≤ g') (hP : P' → P) (hQ : ∀ a, Q a → Q' a)
    (h : GTriple g P t Q) : GTriple g' P' (gweaken hg t) Q' := by
  intro hP'
  exact (gweaken hg t).mono hQ (h (hP hP'))

omit [Preorder G] in
/-- **Sequencing (grades add).** The classic Hoare composition with an
intermediate `Prop` assertion `R`: from `{P} t₁ {_ ↦ R}` at grade `g₁` and
`{R} t₂ {Q}` at grade `g₂`, obtain `{P} (t₁ >>= fun _ => t₂) {Q}` at grade
`g₁ + g₂`. Post-strengthening from `R` to `t₂.wp Q` inside `t₁` uses `t₁.mono` —
this is exactly where bundled monotonicity is needed. -/
theorem seq {α β : Type} {g₁ g₂ : G} {P R : Prop}
    {t₁ : GPredTrans g₁ α} {t₂ : GPredTrans g₂ β} {Q : β → Prop}
    (h₁ : GTriple g₁ P t₁ (fun _ => R))
    (h₂ : GTriple g₂ R t₂ Q) :
    GTriple (g₁ + g₂) P (gbind t₁ (fun _ => t₂)) Q := by
  intro hP
  exact t₁.mono (fun _ hR => h₂ hR) (h₁ hP)

/-! ## 3. A concrete graded demo (`G := ℕ`)

Two unit-cost steps compose to total grade `2` via `seq`, and the grade `1 + 1`
reduces to `2` definitionally, so the composed triple lands at grade `2`. -/

/-- A single unit-**cost** step (grade `1 : ℕ`): a pure WP step that threads its
postcondition at `()`. -/
def stepCost1 : GPredTrans (1 : ℕ) Unit where
  wp Q := Q ()
  mono h hQ := h () hQ

/-- **Demo.** Two unit-cost steps sequence — via `seq` — into a triple whose
grade is the **sum** `1 + 1`. -/
theorem demo_two_steps :
    GTriple ((1 : ℕ) + 1) True (gbind stepCost1 (fun _ => stepCost1)) (fun _ => True) :=
  seq (P := True) (R := True) (t₁ := stepCost1) (t₂ := stepCost1) (Q := fun _ => True)
    (fun _ => trivial) (fun _ => trivial)

/-- The demo's grade is literally `2`: `1 + 1 = 2` in `ℕ`, so `demo_two_steps`
is a triple at grade `2`. -/
theorem demo_grade_is_two : (1 : ℕ) + 1 = 2 := rfl

/-- The same two-step composition, stated directly at grade `2` (using that
`GPredTrans ((1:ℕ)+1) = GPredTrans 2` definitionally), showing the postcondition
threads through **both** steps: the composed WP delivers `Q ()`. -/
theorem demo_wp (Q : Unit → Prop) :
    GTriple (2 : ℕ) (Q ()) (gbind stepCost1 (fun _ => stepCost1)) Q :=
  fun h => h

end CatCrypt.Crypto.SecureCompilation.Ascent.GradedWP
