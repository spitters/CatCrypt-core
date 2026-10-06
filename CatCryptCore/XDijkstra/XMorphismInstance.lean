/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XPostShape


@[expose] public section
set_option autoImplicit false

/-!
# A non-identity `XWPMorphism`: the base-change WP transfer and its relation to graded morphisms

`XPostShape.lean` closes the four axis-laws of the extended-PostShape Dijkstra framework
and, for the monad-morphism axis, ships the identity `XWPMorphism` (`instXWPMorphismId`,
all maps `id`, `transfer` by `rfl`), which shows the shape of the law but transfers
nothing. This module supplies a non-identity `XWPMorphism` — a weakest-precondition
transfer along an effect morphism — and relates the morphism axis to ε-graded monad
morphisms of UC monads. Those morphisms are not defined in this package; the
relation is described structurally below.

## The morphism: base change `StateM σ → StateT σ Option`, at the PostShape level

The instance follows the base change of weakest preconditions in `Std.Do`: the
base-change morphism `θ : StateM σ → StateT σ Option` (run the total state computation,
always succeed) whose WP transfer pushes a success postcondition forward verbatim and
discards the unreachable failure barrel (`PostCond.noThrow`). Here that transfer is at the
abstract `XPostShape` level, between the two shapes

* source `psm = graded G (arg σ pure)` — the total state shape, no exception layer;
* target `psn = graded G (arg σ (except PUnit pure))` — the same state spine with a failure
  barrel added (the `StateT _ Option` shape).

Both shapes have the same state spine `σ` and grade carrier `G × PUnit`, so
`XAssertion psm Ω = XAssertion psn Ω = (σ → Ω)` definitionally and the precondition map
`preMap` is the identity. The postcondition map `postMap` (`θ#`) is the non-identity piece:
it carries an `n`-postcondition to an `m`-postcondition by keeping the success barrel `Q.1`
verbatim and dropping the `PUnit` failure barrel — the `noThrow` pushforward. The transfer
law holds by `rfl` (both WP observations reduce to `x.apply` at the pushed-forward post).

`demo_base_change_transport` exercises it: a concrete state triple `⦃s = 0⦄ incr ⦃s = 1⦄`
over the total shape is transported, by `xwp_morphism`, into the same triple for the
base-changed `θ incr` in the exception-carrying shape.

## Relation to ε-graded monad morphisms

`XWPMorphism` is the weakest-precondition (spec-monad) face of a monad morphism
`θ : m → n`: `transfer` states that WP-observation is natural in `θ` (with
`preMap`/`postMap` = `θ`'s action on pre- and postconditions). An ε-graded monad
morphism of UC monads is an operational refinement of this: a monad morphism
`lift : T₁ → T₂` that preserves `pure`/`bind`/`ucMapSum` and is non-expansive up to an
additive distance cost `ε`, with grades adding under composition, as grades add as
values under `xseq` (`xseq_grade`).

The ungraded `XWPMorphism` corresponds to grade `ε = 0`. Two facts witness this
in-file:

* `thetaX_grade` — the base-change morphism preserves the grade
  (`(thetaX t).grade = t.grade`): it adds zero grade, the `ε = 0` case.
* `thetaX_grade_xseq` — it commutes with the additive grade accumulation of `xseq`
  (`grade (θ (xseq x y)) = grade (θ x) + grade (θ y)`): `θ` is a grade-`0` graded monad
  morphism in the grade axis.

No `UCMonad`/`SPComp` import is needed: the correspondence is structural
(`transfer` ↔ WP-naturality of `lift`; `grade`/`xseq` ↔ the additive `ε`), witnessed
by the two grade lemmas.
-/

namespace CatCrypt.XDijkstra

universe u

variable {G σ Ω : Type} [Preorder Ω]

/-! ## 1. The base-change postcondition map `θ#` (drops the failure barrel)

`postMap` carries a postcondition of the exception-carrying target shape
`graded G (arg σ (except PUnit pure))` to one of the total source shape
`graded G (arg σ pure)`: the success barrel `Q.1 : α → σ → Ω` is kept verbatim
(the two shapes share the `σ → Ω` assertion type), and the `PUnit` failure barrel
is discarded. This is the `PostCond.noThrow` pushforward of `Spec.wp_theta`. -/

/-- **The base-change `PostShape`-map `θ#`.** Keep the success barrel; drop the
`PUnit` failure barrel. `XAssertion` is shared between the two shapes (same state
spine), so `Q.1` is reused with no reindexing. -/
def baseChangePost {α : Type}
    (Q : XPostCond α (.graded G (.arg σ (.except PUnit .pure))) Ω) :
    XPostCond α (.graded G (.arg σ .pure)) Ω :=
  (Q.1, PUnit.unit)

/-! ## 2. The base-change effect morphism on transformers

`thetaX` sends a transformer over the total shape to one over the
exception-carrying shape: it precomposes the WP map with `baseChangePost`, keeps
the grade unchanged, and lifts monotonicity through `baseChangePost` (which
preserves entailment because it forgets the vacuous failure barrel). Observed via
`instXWPSelf`, `thetaX` is the effect morphism `θ` of the `XWPMorphism`. -/

/-- **The base-change morphism `θ` at the transformer level.** Precompose the WP
with `baseChangePost` (push the postcondition forward, dropping the unreachable
failure barrel); grade is carried through unchanged. -/
def thetaX {α : Type}
    (t : XPredTrans (.graded G (.arg σ .pure)) Ω α) :
    XPredTrans (.graded G (.arg σ (.except PUnit .pure))) Ω α where
  apply Q := t.apply (baseChangePost Q)
  grade := t.grade
  mono h := t.mono ⟨fun a => h.1 a, trivial⟩

@[simp] theorem thetaX_apply {α : Type}
    (t : XPredTrans (.graded G (.arg σ .pure)) Ω α)
    (Q : XPostCond α (.graded G (.arg σ (.except PUnit .pure))) Ω) :
    (thetaX t).apply Q = t.apply (baseChangePost Q) := rfl

/-! ## 3. The non-identity `XWPMorphism` instance

`postMap = baseChangePost` (non-identity: it drops the failure barrel); `preMap = id` (the
state spine is unchanged, so the precondition type is shared); `transfer` holds by `rfl`
because both WP observations are `instXWPSelf = id` and `(thetaX x).apply Q` is
`x.apply (baseChangePost Q)` by definition. -/

/-- **The base-change WP morphism.** A non-identity `XWPMorphism`: the postcondition map
`postMap = baseChangePost` discards the failure barrel (the `noThrow` pushforward of
`Spec.wp_theta`), `preMap` is the identity on the shared state-assertion type, and the
transfer law is definitional. -/
instance instXWPMorphismBaseChange :
    XWPMorphism (Ω := Ω)
      (m := XPredTrans (.graded G (.arg σ .pure)) Ω)
      (n := XPredTrans (.graded G (.arg σ (.except PUnit .pure))) Ω)
      (psm := .graded G (.arg σ .pure))
      (psn := .graded G (.arg σ (.except PUnit .pure)))
      (fun {_} t => thetaX t) where
  postMap {_} Q := baseChangePost Q
  preMap P := P
  preMap_mono h := h
  transfer _ _ := rfl

/-! ## 4. Demonstration: a total state triple transported into the exception shape

`incrT` is the WP transformer of the total state step `s ↦ s + 1` at the total
shape. The triple `⦃s = 0⦄ incrT ⦃s = 1⦄` (a `XTriple` via `instXWPSelf`) is
transported by `xwp_morphism` along the base-change morphism into the same triple
for `thetaX incrT` in the exception-carrying shape. -/

/-- The WP transformer of the total state step `s ↦ s + 1`, at shape
`graded ℕ (arg ℕ pure)`. -/
def incrT : XPredTrans (.graded ℕ (.arg ℕ .pure)) Prop Unit where
  apply Q := fun s => Q.1 () (s + 1)
  grade := (0, PUnit.unit)
  mono h := fun s => h.1 () (s + 1)

/-- **Morphism-transfer demo.** The total state triple `⦃s = 0⦄ incrT ⦃s = 1⦄` is
transported, along the base-change morphism, into the same triple for `thetaX incrT` in the
exception-carrying shape `graded ℕ (arg ℕ (except PUnit pure))`. The failure barrel of the
target postcondition (`fun _ => True`) is discarded by `baseChangePost`; the residual
verification condition is the total state step. -/
theorem demo_base_change_transport :
    XTriple (Ω := Prop)
      (ps := .graded ℕ (.arg ℕ (.except PUnit .pure)))
      (m := XPredTrans (.graded ℕ (.arg ℕ (.except PUnit .pure))) Prop)
      (α := Unit)
      (fun s => s = 0)
      (thetaX incrT)
      ((fun _ s => s = 1, (fun _ => True, PUnit.unit)) :
        XPostCond Unit (.graded ℕ (.arg ℕ (.except PUnit .pure))) Prop) := by
  refine xwp_morphism (Ω := Prop)
    (m := XPredTrans (.graded ℕ (.arg ℕ .pure)) Prop)
    (n := XPredTrans (.graded ℕ (.arg ℕ (.except PUnit .pure))) Prop)
    (psm := .graded ℕ (.arg ℕ .pure))
    (psn := .graded ℕ (.arg ℕ (.except PUnit .pure)))
    (θ := fun {_} t => thetaX t) (x := incrT)
    (P₀ := fun s => s = 0)
    (Q := (fun _ s => s = 1, (fun _ => True, PUnit.unit))) ?_
  intro s hs
  show s + 1 = 1
  omega

/-! ## 5. The graded bridge: `thetaX` at grade `ε = 0`

These two lemmas witness, in-file, the relation described in the module docstring:
the ungraded `XWPMorphism` corresponds to an ε-graded morphism at `ε = 0`. `thetaX`
carries the grade through unchanged (adds `0`), and it commutes with `xseq`'s
additive grade accumulation, the value-level counterparts of grade-`0` packaging and
of additive composition of graded morphisms. -/

/-- **`thetaX` adds zero grade** — it preserves the grade. This is the `ε = 0`
face of the graded morphism: the WP transfer charges no extra grade. -/
theorem thetaX_grade {α : Type}
    (t : XPredTrans (.graded G (.arg σ .pure)) Ω α) :
    (thetaX t).grade = t.grade := rfl

/-- **`thetaX` commutes with additive grade accumulation.** Sequencing under `xseq`
and then transporting equals transporting each step and adding the grades:
`grade (θ (xseq x y)) = grade (θ x) + grade (θ y)`. So `θ` is a grade-`0` *graded*
monad morphism in the XDijkstra grade axis, corresponding to
an ε-graded morphism at `ε = 0`. -/
theorem thetaX_grade_xseq [Add G] {α β : Type}
    (x : XPredTrans (.graded G (.arg σ .pure)) Ω α)
    (y : XPredTrans (.graded G (.arg σ .pure)) Ω β) :
    (thetaX (xseq x y)).grade = (thetaX x).grade + (thetaX y).grade := rfl

end CatCrypt.XDijkstra
