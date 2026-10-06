/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCryptCore.XDijkstra.Rel.XRelSpecMonad


@[expose] public section
set_option autoImplicit false

/-!
# `relmvcgen`: the relational-VC tactic for the coupling-spec-monad

`relmvcgen` is the relational verification-condition generator for the coupling-spec monad
of `XRelSpecMonad.lean`. It fires `relBind_spec` / `relSpec_seq` at each `bind` node of a
coupled bind-chain, reducing an end-to-end coupling goal to the per-hop coupling leaves and
the summed grade — the tactic form of `relSpec3_auto` / `relSpec3_auto_via_relBind`. It is
the counterpart of `xmvcgen` (`XMvcgen.lean`) for the coupling axis: `xmvcgen` normalizes a
WP through the product `xseq` and threads only the grade; `relmvcgen` threads the whole
coupling through the monad-over-pairs bind.

## What `relmvcgen` does

Given a goal of the form

* `RelSpec (relBind (δ := δ) m k₁ k₂) S`, or
* `RelSpecTriple (ε + δ) S (RelQ0.bind' c k₁) (RelQ0.bind' c' k₂)`
  (equivalently `XRelTripleQ0 …`, since `RelSpecTriple = XRelTripleQ0`),

`relmvcgen` applies the composition lemma backward — `apply relSpec_seq` (and, for the
`relBind`-phrased shape, `apply relBind_spec`) — splitting the coupling of the bound
programs into

1. the prefix coupling `RelSpecTriple ε ?R c c'` (at a fresh intermediate relation `?R`),
   and
2. the continuation coupling `∀ a b, ?R a b → RelSpecTriple δ S (k₁ a) (k₂ b)`,

with the grade `ε + δ` read off the type index (the sum is in the object, no separate
accumulation pass, unlike `xmvcgen`'s `xwp_graded_bind`). It then recurses on the prefix,
so a length-`n` bind-chain unfolds into `n` per-hop coupling leaves plus the `n-1`
continuation obligations, the leaves `relSpec3_auto` composes by hand.

The tactic is `repeat first | apply relBind_spec | apply relSpec_seq`: `apply` operates on
the main goal, and each application puts the prefix subgoal first, so `repeat` drills down
the prefix chain and stops at the innermost non-`bind` leaf, leaving all per-hop leaves as
the residual goals.

## Calling convention — the intermediate-relation metavariable

An intermediate relation `R` in `relBind_spec`/`relSpec_seq` appears only in the two
premises, never in the conclusion `RelSpec (relBind m k₁ k₂) S`. So the backward step
cannot infer it and leaves it as a metavariable `?R` shared between the prefix goal
`RelSpec m ?R` and the continuation goal `∀ a b, ?R a b → …`.

**Why `apply`, not `refine`.** `refine relSpec_seq ?_ ?_` fails here — its elaborator
raises `don't know how to synthesize implicit argument R`, because `R` is an implicit that
unification cannot pin from the conclusion and it was not written as a hole. `apply` defers
`R` as a dependent metavariable goal (occurring in the sibling premise goals), and that
goal auto-resolves once a premise is discharged with a concrete-relation hypothesis, so it
never has to be proved by hand.

`?R` is pinned when the leaf is discharged: `exact hᵢ` against a per-hop hypothesis whose
relation is concrete assigns `?R`, and because the metavariable is shared, the matching
continuation goal is simultaneously specialized and the deferred `R` goal disappears. The
convention is:

> Run `relmvcgen`, then discharge each residual leaf with the corresponding per-hop coupling
> hypothesis (`exact h₁`; `intro a b hab; exact h₂ a b hab`; …). The leaves are produced
> innermost-prefix-first, then continuations outermost-last. No explicit `(R := …)` is
> needed — the leaf hypotheses pin every intermediate relation.

To fix the relations up front — e.g. to inspect the intermediate goals — `refine
relSpec_seq (R := R₀) ?_ ?_` works; `relmvcgen` otherwise defers them.

The demos below (`relDemo3_tac`, `relDemo3_via_relBind_tac`, `relDemo5_tac`,
`relDemo3_sdistr_tac`) reproduce `XRelSpecMonad.relSpec3_auto` and its variants with
`relmvcgen` in place of the hand-nested `relBind_spec`, leaving the per-hop leaves.
-/

namespace CatCrypt.XDijkstra

open scoped ENNReal
open CatCrypt CatCrypt.Prob

/-! ## 1. The `relmvcgen` tactic

`relmvcgen` repeatedly applies the coupling-composition lemma backward at each `bind` node,
recursing on the prefix, until only atomic per-hop coupling leaves remain. It tries
`relBind_spec` (the `RelSpec`/`relBind` phrasing) and `relSpec_seq` (the
`RelSpecTriple`/`RelQ0.bind'` phrasing), so it fires on both the spec-monad and the
raw-triple presentations of a coupled bind-chain. -/

/-- **Relational verification-condition generator for the coupling-spec-monad.** On a goal
`RelSpec (relBind m k₁ k₂) S` or `RelSpecTriple (ε + δ) S (RelQ0.bind' c k₁) (RelQ0.bind' c' k₂)`,
fires the coupling-composition lemma backward at every `bind` node (`relBind_spec` /
`relSpec_seq`), reducing the end-to-end coupling to the per-hop coupling leaves; the grade
`ε + δ` is threaded in the type index. Intermediate per-hop relations are left as
metavariables, pinned when each leaf is discharged (see the module docstring's calling
convention). -/
macro "relmvcgen" : tactic =>
  `(tactic| repeat first
    | apply relBind_spec
    | apply relSpec_seq)

/-! ## 2. Demos — `relmvcgen` replaces the hand-nested `relBind_spec`

Each demo reproduces a composition from `XRelSpecMonad.lean`, but the coupling composition —
there a hand-nested `relBind_spec (relBind_spec h₁ h₂) h₃` — is produced by `relmvcgen`. The
tactic fires, leaves the per-hop coupling leaves, and each is discharged from its leaf
hypothesis, which simultaneously pins the intermediate relation metavariable. -/

section Demo
variable {T : Type → Type} [RelQ0 T]
variable {α₀ β₀ α₁ β₁ α₂ β₂ α₃ β₃ α₄ β₄ α₅ β₅ : Type}

/-- **3-hop coupling composition by `relmvcgen`** (`RelSpecTriple`/`bind'` phrasing). This is
`XRelSpecMonad.relSpec3_auto` with `relmvcgen` in place of `relSpec_seq (relSpec_seq h₁ h₂) h₃`:
the tactic fires `relSpec_seq` twice, leaving the three per-hop leaves, discharged from
`h₁`, `h₂`, `h₃`. -/
theorem relDemo3_tac {ε₁ ε₂ ε₃ : ℝ≥0∞}
    {R₀ : α₀ → β₀ → Prop} {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop}
    {m₁ : T α₀} {m₂ : T β₀}
    {k₁ : α₀ → T α₁} {k₂ : β₀ → T β₁}
    {l₁ : α₁ → T α₂} {l₂ : β₁ → T β₂}
    (h₁ : RelSpecTriple ε₁ R₀ m₁ m₂)
    (h₂ : ∀ a b, R₀ a b → RelSpecTriple ε₂ R₁ (k₁ a) (k₂ b))
    (h₃ : ∀ a b, R₁ a b → RelSpecTriple ε₃ R₂ (l₁ a) (l₂ b)) :
    RelSpecTriple ((ε₁ + ε₂) + ε₃) R₂
      (RelQ0.bind' (RelQ0.bind' m₁ k₁) l₁) (RelQ0.bind' (RelQ0.bind' m₂ k₂) l₂) := by
  relmvcgen
  · exact h₁                         -- leaf 1: prefix coupling, pins the innermost relation
  · intro a b hab; exact h₂ a b hab  -- leaf 2: hop `k`, pins the middle relation
  · intro a b hab; exact h₃ a b hab  -- leaf 3: hop `l`

/-- **3-hop coupling composition by `relmvcgen`** (`RelSpec`/`relBind` phrasing). This is
`XRelSpecMonad.relSpec3_auto_via_relBind` with `relmvcgen` in place of the hand-nested
`relBind_spec (relBind_spec h₁ h₂) h₃`. -/
theorem relDemo3_via_relBind_tac {ε₁ ε₂ ε₃ : ℝ≥0∞}
    {R₀ : α₀ → β₀ → Prop} {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop}
    {m₁ : T α₀} {m₂ : T β₀}
    {k₁ : α₀ → T α₁} {k₂ : β₀ → T β₁}
    {l₁ : α₁ → T α₂} {l₂ : β₁ → T β₂}
    (h₁ : RelSpecTriple ε₁ R₀ m₁ m₂)
    (h₂ : ∀ a b, R₀ a b → RelSpecTriple ε₂ R₁ (k₁ a) (k₂ b))
    (h₃ : ∀ a b, R₁ a b → RelSpecTriple ε₃ R₂ (l₁ a) (l₂ b)) :
    RelSpec
      (relBind (δ := ε₃)
        (relBind (δ := ε₂) (⟨m₁, m₂⟩ : RelPT (T := T) ε₁ α₀ β₀) k₁ k₂) l₁ l₂) R₂ := by
  relmvcgen
  · exact h₁
  · intro a b hab; exact h₂ a b hab
  · intro a b hab; exact h₃ a b hab

/-- **5-hop coupling composition by `relmvcgen`** — the scaling demo. Five coupled hops
compose into `RelSpecTriple (((ε₁ + ε₂) + ε₃ + ε₄) + ε₅) R₄` of the five-fold bound pair;
`relmvcgen` fires `relSpec_seq` four times, leaving the five per-hop leaves. The tactic call
does not change with depth. -/
theorem relDemo5_tac {ε₁ ε₂ ε₃ ε₄ ε₅ : ℝ≥0∞}
    {R₀ : α₀ → β₀ → Prop} {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop}
    {R₃ : α₃ → β₃ → Prop} {R₄ : α₄ → β₄ → Prop}
    {m₁ : T α₀} {m₂ : T β₀}
    {k₁ : α₀ → T α₁} {k₂ : β₀ → T β₁}
    {l₁ : α₁ → T α₂} {l₂ : β₁ → T β₂}
    {p₁ : α₂ → T α₃} {p₂ : β₂ → T β₃}
    {q₁ : α₃ → T α₄} {q₂ : β₃ → T β₄}
    (h₁ : RelSpecTriple ε₁ R₀ m₁ m₂)
    (h₂ : ∀ a b, R₀ a b → RelSpecTriple ε₂ R₁ (k₁ a) (k₂ b))
    (h₃ : ∀ a b, R₁ a b → RelSpecTriple ε₃ R₂ (l₁ a) (l₂ b))
    (h₄ : ∀ a b, R₂ a b → RelSpecTriple ε₄ R₃ (p₁ a) (p₂ b))
    (h₅ : ∀ a b, R₃ a b → RelSpecTriple ε₅ R₄ (q₁ a) (q₂ b)) :
    RelSpecTriple ((((ε₁ + ε₂) + ε₃) + ε₄) + ε₅) R₄
      (RelQ0.bind' (RelQ0.bind' (RelQ0.bind' (RelQ0.bind' m₁ k₁) l₁) p₁) q₁)
      (RelQ0.bind' (RelQ0.bind' (RelQ0.bind' (RelQ0.bind' m₂ k₂) l₂) p₂) q₂) := by
  relmvcgen
  · exact h₁
  · intro a b hab; exact h₂ a b hab
  · intro a b hab; exact h₃ a b hab
  · intro a b hab; exact h₄ a b hab
  · intro a b hab; exact h₅ a b hab

end Demo

/-! ### `relmvcgen` on `SDistr`

At `SDistr` (`liftR := liftRApprox`, the `ε`-approximate sub-coupling), the tactic composes
three coupled hops into the end-to-end coupling `XRelTripleQ0 (T := SDistr) (ε₁ + ε₂ + ε₃)`
from the three per-hop leaves — the tactic form of `XRelSpecMonad.relDemo3_sdistr`. -/

section SDistrDemo
variable {α₀ β₀ α₁ β₁ α₂ β₂ : Type}

/-- **3-hop coupling on `SDistr`, by `relmvcgen`.** `RelSpecTriple = XRelTripleQ0`, so this
is an end-to-end `ε`-approximate coupling of a three-step coupled reduction on the crypto
monad, assembled from the per-hop leaves by the tactic. -/
theorem relDemo3_sdistr_tac {ε₁ ε₂ ε₃ : ℝ≥0∞}
    {R₀ : α₀ → β₀ → Prop} {R₁ : α₁ → β₁ → Prop} {R₂ : α₂ → β₂ → Prop}
    {m₁ : SDistr α₀} {m₂ : SDistr β₀}
    {k₁ : α₀ → SDistr α₁} {k₂ : β₀ → SDistr β₁}
    {l₁ : α₁ → SDistr α₂} {l₂ : β₁ → SDistr β₂}
    (h₁ : XRelTripleQ0 (T := SDistr) ε₁ R₀ m₁ m₂)
    (h₂ : ∀ a b, R₀ a b → XRelTripleQ0 (T := SDistr) ε₂ R₁ (k₁ a) (k₂ b))
    (h₃ : ∀ a b, R₁ a b → XRelTripleQ0 (T := SDistr) ε₃ R₂ (l₁ a) (l₂ b)) :
    XRelTripleQ0 (T := SDistr) ((ε₁ + ε₂) + ε₃) R₂
      (RelQ0.bind' (RelQ0.bind' m₁ k₁) l₁) (RelQ0.bind' (RelQ0.bind' m₂ k₂) l₂) := by
  relmvcgen
  · exact h₁
  · intro a b hab; exact h₂ a b hab
  · intro a b hab; exact h₃ a b hab

end SDistrDemo

end CatCrypt.XDijkstra
