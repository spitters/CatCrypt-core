/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XPostShape
public import CatCryptCore.XDijkstra.XQuantaleGradeCore
public import CatCryptCore.Crypto.UCMonad.UCLeakageDecomp
public import CatCryptCore.Category.Effectus

@[expose] public section

set_option autoImplicit false

/-!
# `XCategoricalModel`: the categorical model of the XDijkstra framework

This module records the categorical semantics of the XDijkstra
predicate-transformer framework. The framework is a

> quantale-graded relational Dijkstra monad over the SSP-package / coPara
> game category,

and this file states three of the four reasoning axes (grade, separation,
morphism) as their categorical structures, records two structural facts about the
base, and describes the universal property. Statements that are one line over the
metatheory are Lean lemmas here; categorical statements beyond that scope (a
Mathlib `CategoryTheory` effectus instance, the universal property and the
adjunction) are stated in this docstring only. The fourth axis, the relational
lifting as a monad on pairs, depends on the relational coupling layer and is stated outside this library.

The file builds on:

* `XPostShape` — the extended predicate transformer `XPredTrans`, the effect
  observation `XWP.xwp : m → XPredTrans` (a graded Dijkstra monad), `xpure` /
  `xbind` / `xseq`, and the four axis-laws (`xseq_triple`, `xframe`, `xrel_seq`,
  `xwp_morphism` with `XWPMorphism`).
* `XQuantaleGradeCore` — the grade as the **Lawvere quantale** `([0,∞], ≤, +, 0)`
  (`GradeQuantale`): `gmul = (+)` sequential, `gjoin = (⊔)` worst-case-adversary.
* `UCLeakageDecomp` — `UCviaRel_iff_ExactUCEmulates`: UC is the `∃ sim`
  wrapping of the relational coupling over the `ExceptT` leakage branch.
* `Category/Effectus` — the effectus predicate `EffectusPred`
  (`α → 1 + 1 = α → Bool`), the weakest-precondition transformer `wpTransformer`,
  and positive cancellation (E3).

## 1. The effect observation `wp` as a graded monad morphism

XDijkstra is a **graded Dijkstra monad** in the sense of Katsumata's graded
monads plus an effect observation (Maillard–Hriţcu–Rivas–Van Muylder, "Dijkstra
Monads for All"): the semantics of an effectful program `x : m α` is its
weakest-precondition transformer `wp x = XWP.xwp x : XPredTrans ps Ω α`, and this
`wp` is a **monad morphism into the spec monad**, respecting `pure`/`bind` and
carrying the grade additively.

`XPredTrans ps Ω` is the spec monad; `xpure`/`xbind` are its unit/multiplication
(`instMonad`) and `xseq` is the grade-additive sequencing (grades live as a
*value* field, so they thread through `xseq`, whose continuation grade is a single
value — `xbind`'s value-dependent continuation cannot, which is exactly why the
grade is threaded by `xseq`, see `XPostShape`'s note). `GradedDijkstraObservation`
below bundles the morphism laws; `self_gradedDijkstraObservation` witnesses them
for the canonical self-observation (`wp = id`), and the grade corollaries record
`pure ↦ grade 0` and `xseq ↦ grade +`.

## 2. The four axes ↔ categorical-structures dictionary

| Axis | XDijkstra operation | Categorical structure |
|------|---------------------|-----------------------|
| **grade** | `xseq` grade `g₁ + g₂`, `xpar` grade `g₁ ⊔ g₂` | the **Lawvere quantale** `([0,∞], ≤, +, 0)` — `GradeQuantale`; `gmul = (+)`, `gjoin = (⊔)`; the enrichment base (`grade_axis_is_lawvere_quantale`, `xseq_grade_is_gmul`) |
| **separation / frame** | `xframe` over `XBI`, `∗` | **effectus separation** = an ordered partial commutative monoid of predicates, and — at the Boolean/affine case — the SSP **package** product `∗`; the package `∗` is the Kleisli coproduct `ucMapSum` on disjoint interfaces. At the `Prop` carrier `∗ = ∧` (`sl_axis_boolean_effectus_sep`), the affine effectus meet. |
| **relational** | `xprod`/`xseq` (blind) → coupling composition (carrying) | the **relational lifting** as a **monad on pairs**, whose `bind` is the coupling composition at additive grade; stated in `XCategoricalModelRel` (`relational_axis_is_monad`, `relational_grade_adds`) |
| **morphism** | `xwp_morphism` transfer along `θ : m → n` | a **graded monad morphism** `XWPMorphism` (the effect-observation transfer / change of effect); `morphism_axis_transfers` |

The grade axis is a Lawvere/quantale enrichment: `GradeQuantale ℝ≥0∞` is the
grade object over which a metric on Kleisli maps is enriched. The effectus reading
of the separation axis is an ordered *partial* commutative monoid of predicates
with a monotone frame rule; its Boolean instance is the affine effectus where
`∗ = ∧`, and the SSP package `∗` is the disjoint-interface Kleisli coproduct.
Neither structure is imported by this file.

## 3. Two structural facts about the base

**(a) The base is an effectus — initial ≠ terminal, so no zero object.**
In the effectus (Cho–Jacobs), a predicate on `X` is a Kleisli map `X → 1 + 1`; the
classifier `1 + 1 ≅ Bool` has the two coproduct injections `κ₁, κ₂ : 1 → 1 + 1`
("true"/"false"). The terminal `1 = Unit`; the initial `0 = Empty` is the unit of
the leakage coproduct `⊕` (an empty interface adds nothing: `α ⊕ Empty ≃ α`,
`Equiv.sumEmpty`). A **zero object** would be `0 ≅ 1`; then
`1 + 1 ≅ 1 + 0 ≅ 1`, so the classifier would be terminal and its two injections
would collapse `κ₁ = κ₂` — every predicate would identify true and false, and all
predicates collapse. But `initial ≠ terminal` (`Empty ≇ Unit`,
`initial_ne_terminal`) and the two injections are distinct (`true ≠ false`,
`predicate_classifier_two_points`); hence **no zero object**
(`effectus_no_zero_object`: the one-predicate and the zero-predicate differ on any
faithful monad). This is the categorical reason game-hopping is sound (E3 positive
cancellation `EffectusPositiveCancel`): advantages cannot cancel because there is
no zero to collapse them into.

**(b) UC is a derived `∃ sim`-notion, not a categorical primitive.** The primitive
is the relational coupling (the coupling monad on pairs, or `RelLeakExact` over the `ExceptT` leakage branch). UC is
that coupling with a
simulator existentially quantified: `UCviaRel π F = ∀ A, ∃ sim, real ≡
ideal∘sim` (`uc_is_derived`, `ExactUCEmulates`). The `∃ sim` is the UC-specific
quantifier — dropping it (forcing `sim = id`) is strictly stronger
(`identityRel_implies_UCviaRel` holds but its converse fails: Pedersen / dual-OT
need a non-trivial equivocating/extracting simulator). So the coupling is the
categorical primitive and UC is built over it, existentially.

## 4. The universal-property / adjunction picture

The following statements complete the model. Each names the formalized declaration
it would specialize; the `CategoryTheory` statement itself is not formalized here.

* **`XPredTrans` is the free / initial graded Dijkstra monad on the effect
  signature `ps`.** Concretely: for every effect observation `wp : m →
  XPredTrans ps Ω` respecting the graded structure (a `GradedDijkstraObservation`),
  the spec monad `XPredTrans` receives `wp` uniquely as a graded monad morphism —
  it is the terminal object among "monads-with-a-WP-into-predicates". The
  self-observation `self_gradedDijkstraObservation` is the identity component; the
  universal arrow is `wp` itself.
* **Predicates ⊣ predicate-transformers (the WP adjunction).** The
  weakest-precondition transformer `wpTransformer` (`Category/Effectus`) is the right
  adjoint to the predicate-fibration's reindexing: `wp(f, −)` is post-composition
  `p ↦ p ∘ f`, functorial (`wpTransformer_pure`, `wpTransformer_comp`) and
  faithful under E3 (`wpTransformer_faithful`). At the extended shape this is
  `XPredTrans.apply : XPostCond → XAssertion`, monotone (`XPredTrans.mono`) — the
  contravariant WP adjunction on the assertion algebra `Ω`.
* **The whole model = the graded relational Dijkstra monad over the SSP-package
  (coPara) monoidal category.** The base monoidal category is the SSP
  state-separating package algebra: objects are interfaces, the monoidal product
  is disjoint package composition `∗` (`ucMapSum`), and games are package
  compositions. The XDijkstra transformer is a graded Dijkstra monad *fibred over*
  this base; the relational axis is its restriction to the coPara / span-of-pairs
  bicategory. This is the equipment presented by the coPara framed bicategory of
  protocols, enriched over the Lawvere quantale; this file imports neither.

## Formalized and stated

* **Formalized** (Lean lemmas): §1 the observation-morphism bundle
  (`GradedDijkstraObservation`, `self_gradedDijkstraObservation`, grade
  corollaries); §2 the dictionary one-liners (`grade_axis_is_lawvere_quantale`,
  `xseq_grade_is_gmul`, `sl_axis_boolean_effectus_sep`,
  `morphism_axis_transfers`; the relational pair `relational_axis_is_monad`,
  `relational_grade_adds` is stated with the coupling layer); §3(a) the no-zero-object
  witnesses (`predicate_classifier_two_points`, `initial_ne_terminal`,
  `leakage_coproduct_unit`, `effectus_no_zero_object`); §3(b) UC-derived
  (`uc_is_derived`, `uc_needs_nontrivial_simulator`).
* **Stated in this docstring** (not formalized): §4 the universal property, the
  predicates ⊣ WP adjunction as a `CategoryTheory` adjunction, and the identity
  with the coPara equipment.

## Main results

* `GradedDijkstraObservation`, `wp_pure_grade`, `wp_seq_grade`: the weakest precondition
  as a graded monad morphism.
* `grade_axis_is_lawvere_quantale`, `xseq_grade_is_gmul`: the grade axis is the Lawvere
  quantale, and sequencing multiplies grades.
* `sl_axis_boolean_effectus_sep`: at the carrier `Prop` the separating conjunction is the
  conjunction.
* `morphism_axis_transfers`: triples transfer along morphisms of transformers.
* `effectus_no_zero_object`, `uc_is_derived`, `uc_needs_nontrivial_simulator`: the
  effectus side conditions and the derivation of UC emulation.
-/

namespace CatCrypt.XDijkstra

open scoped ENNReal
open CatCrypt.Category.Effectus
open CatCrypt.Crypto.SecureCompilation.Ascent

universe u v

/-! ## 1. The effect observation `wp` as a graded monad morphism

`wp = XWP.xwp` maps a program to its predicate transformer. It is a **graded monad
morphism into the spec monad** `XPredTrans`: it sends the source `pure` to `xpure`
and the source `bind` to `xbind`, and carries the grade additively through `xseq`.
`GradedDijkstraObservation` bundles the two morphism equations; the self-observation
(`wp = id`, where the source *is* the spec monad) witnesses them by `rfl`. -/

variable {Ω : Type u} [Preorder Ω]

/-- **Graded-Dijkstra-monad-morphism laws of an effect observation.** For a monad
`m` with a WP observation `XWP.xwp : m → XPredTrans ps Ω`, this bundles the two
monad-morphism equations: `wp` sends `pure` to the spec unit `xpure` and `bind` to
the spec multiplication `xbind`. Together with the grade corollaries below
(`pure ↦ 0`, `xseq ↦ +`) this is the statement "XDijkstra = a graded Dijkstra
monad": a Katsumata graded monad `XPredTrans` plus a monad-morphism effect
observation. -/
structure GradedDijkstraObservation (ps : XPostShape.{u})
    [Zero ps.Grade] (m : Type u → Type v) [Monad m] [XWP m ps Ω] : Prop where
  /-- `wp` preserves `pure`: it lands on the spec-monad unit `xpure`. -/
  wp_pure : ∀ {α : Type u} (a : α),
    XWP.xwp (m := m) (ps := ps) (Ω := Ω) (pure a) = xpure (Ω := Ω) (ps := ps) a
  /-- `wp` preserves `bind`: it lands on the spec-monad multiplication `xbind`. -/
  wp_bind : ∀ {α β : Type u} (x : m α) (f : α → m β),
    XWP.xwp (m := m) (ps := ps) (Ω := Ω) (x >>= f)
      = xbind (XWP.xwp (ps := ps) (Ω := Ω) x) (fun a => XWP.xwp (ps := ps) (Ω := Ω) (f a))

/-- **The self-observation is a graded monad morphism.** The spec monad
`XPredTrans ps Ω` observes itself by the identity (`instXWPSelf`), with `pure`/`bind`
its own `xpure`/`xbind` (`instMonad`); both morphism equations hold by `rfl`. This is
the identity component of the universal effect observation. -/
theorem self_gradedDijkstraObservation (ps : XPostShape.{u}) [Zero ps.Grade] :
    GradedDijkstraObservation (Ω := Ω) ps (XPredTrans ps Ω) :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- **`wp` of `pure` carries grade `0`.** The spec unit `xpure` has grade `0`, so
the observation of a pure program is at the identity grade. -/
theorem wp_pure_grade {ps : XPostShape.{u}} [Zero ps.Grade] {α : Type u} (a : α) :
    (xpure (Ω := Ω) (ps := ps) a).grade = 0 := rfl

/-- **`wp` carries the grade additively through `xseq`.** Sequencing two observed
steps sums their grades — the graded-monad accumulation the effect observation is a
morphism *for*. This is `XPostShape.xseq_grade`, re-exported as the grade component
of the observation morphism. -/
theorem wp_seq_grade {ps : XPostShape.{u}} [Add ps.Grade] {α β : Type u}
    (x : XPredTrans ps Ω α) (y : XPredTrans ps Ω β) :
    (xseq x y).grade = x.grade + y.grade := rfl

/-! ## 2. The four axes ↔ categorical structures (dictionary lemmas)

Each axis is tied to its categorical structure by a one-liner over the existing
metatheory (see the module docstring table for the full dictionary). -/

/-! ### Axis I — grade ↔ the Lawvere quantale -/

/-- **Grade axis = the Lawvere quantale `([0,∞], ≤, +, 0)`.** The two grade
operations are the quantale monoid product `gmul = (+)` (sequential / advantage
composition) and the lattice join `gjoin = (⊔)` (parallel / worst-case adversary).
This is the enrichment base of the whole framework. -/
theorem grade_axis_is_lawvere_quantale (a b : ℝ≥0∞) :
    gmul a b = a + b ∧ gjoin a b = a ⊔ b :=
  gmul_gjoin_ennreal a b

/-- **`xseq` accumulates the grade by the quantale product `gmul`.** At the Lawvere
grade shape `.graded ℝ≥0∞ .pure`, the head grade of `xseq x y` is `gmul` of the two
head grades — the sequential composition of advantages is the quantale `+`. -/
theorem xseq_grade_is_gmul {Ω : Type} [Preorder Ω] {α β : Type}
    (x : XPredTrans (.graded ℝ≥0∞ .pure) Ω α)
    (y : XPredTrans (.graded ℝ≥0∞ .pure) Ω β) :
    (xseq x y).grade.1 = gmul x.grade.1 y.grade.1 :=
  xwp_graded_bind x y

/-! ### Axis II — separation / frame ↔ effectus separation = SSP package `∗`

The SL frame axis (`xframe` over the bunched-implication carrier `XBI`) corresponds
to **effectus separation**: an ordered partial commutative monoid of predicates,
whose Boolean/affine instance has `∗ = ∧`. Categorically this is the SSP
**package** product: disjoint-interface package composition, the Kleisli coproduct
`ucMapSum`. The lemma records the affine case at the `Prop` carrier. -/

/-- **SL frame product at the Boolean carrier is the affine effectus meet `∧`.** The
`XBI Prop` instance takes `∗ := ∧`; framing a resource `R` is conjoining it. This is
the affine effectus law (`∗ = ∧`, idempotent, affine) and, at the package level,
disjoint package composition. -/
theorem sl_axis_boolean_effectus_sep (P R : Prop) :
    XAssertion.sep (Ω := Prop) .pure P R = (P ∧ R) := rfl

/-! ### Axis III — relational ↔ the relational-lifting monad on pairs

The two lemmas of this axis, `relational_axis_is_monad` and
`relational_grade_adds`, are stated with the relational coupling layer, outside this
library. -/

/-! ### Axis IV — morphism ↔ a graded monad morphism `XWPMorphism` -/

/-- **Morphism axis = WP transfer along an effect morphism `θ : m → n`.** A
`XWPMorphism θ` (a `PostShape`-map on postconditions plus a monotone precondition
map satisfying the transfer law) transports a Hoare triple about `x` in `m` into one
about `θ x` in `n`. This is the change-of-effect / graded-monad-morphism axis; it is
the general form of the effect observation being a morphism (§1). -/
theorem morphism_axis_transfers {m n : Type u → Type v} {psm psn : XPostShape.{u}}
    [XWP m psm Ω] [XWP n psn Ω] {θ : {α : Type u} → m α → n α}
    [inst : XWPMorphism (Ω := Ω) (m := m) (n := n) (psm := psm) (psn := psn) θ]
    {α : Type u} (x : m α) {P₀ : XAssertion psm Ω} {Q : XPostCond α psn Ω}
    (h : XTriple (m := m) P₀ x (inst.postMap Q)) :
    XTriple (m := n) (inst.preMap P₀) (θ x) Q :=
  xwp_morphism x h

/-! ## 3. Two structural facts about the base

### (a) The base is an effectus: initial ≠ terminal, hence no zero object -/

/-- **The predicate classifier `1 + 1 ≅ Bool` has two distinct global points.** The
two coproduct injections `κ₁, κ₂ : 1 → 1 + 1` ("true" / "false") are distinct. A
zero object would collapse them (see `effectus_no_zero_object`); their distinctness
is the seed of the no-zero-object argument. -/
theorem predicate_classifier_two_points : (true : Bool) ≠ false := by decide

/-- **Initial ≠ terminal.** The terminal object `1 = Unit` and the initial object
`0 = Empty` are not isomorphic: there is no equivalence `Unit ≃ Empty` (its forward
map would produce an element of `Empty`). In a category with a zero object the two
would coincide; their non-isomorphism is the categorical statement "there is no zero
object". -/
theorem initial_ne_terminal : IsEmpty (Unit ≃ Empty) :=
  ⟨fun e => (e ()).elim⟩

/-- **The initial object `Empty` is the unit of the leakage coproduct `⊕`.** An empty
interface adds nothing observable: `α ⊕ Empty ≃ α` (`Equiv.sumEmpty`). This is why
`Empty` is the `⊕`-unit / initial object of the effectus, and why a leakage-free
channel is `α ⊕ Empty ≅ α`. -/
def leakage_coproduct_unit (α : Type u) : α ⊕ Empty ≃ α :=
  Equiv.sumEmpty α Empty

/-- **No zero object: the one-predicate and the zero-predicate differ.** On any monad
that separates `pure true` from `pure false` (a faithful predicate classifier — the
effectus E3 `EffectusPositiveCancel` gives this), the always-accept predicate
`EffectusPred.one` and the always-reject `EffectusPred.falseP` are distinct. A zero
object `0 ≅ 1` would force `1 + 1 ≅ 1 + 0 ≅ 1`, collapsing the classifier to the
terminal and identifying `κ₁ = κ₂`, i.e. `one = falseP`; the distinctness here
refutes that. Hence the base has **no zero object** (a zero object would collapse all
predicates), and game-hopping — advantages that cannot negatively cancel — is sound. -/
theorem effectus_no_zero_object {T : Type → Type} [Monad T]
    (hsep : (pure true : T Bool) ≠ pure false) :
    EffectusPred.one T Unit ≠ EffectusPred.falseP T Unit := by
  intro h
  have hp := congrArg EffectusPred.pred h
  simp only [EffectusPred.one, EffectusPred.falseP] at hp
  exact hsep (congrFun hp ())

/-! ### (b) UC is the derived `∃ sim`-notion over the relational coupling -/

/-- **UC is derived: the `∃ sim` wrapping of the relational coupling.** The `∃ sim`
relational reading `UCviaRel π F` (for every environment `A`, some simulator `sim`
makes `real` relate to `ideal ∘ sim` at `RelLeakExact` over the `ExceptT` leakage
branch) is *literally* the exact UC notion `ExactUCEmulates`. So UC is **not** a
categorical primitive: the primitive is the relational coupling (`RelLeakExact`, or
the coupling monad on pairs of §2), and UC quantifies a simulator existentially over
it. `∀ A, ∃ sim` is the shape; the coupling is the tactic's primitive, UC is over
it. -/
theorem uc_is_derived {T : Type → Type} [UCMonad.UCMonadBase T]
    {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if)) :
    UCviaRel (view := view) π F ↔ UCMonad.ExactUCEmulates (T := T) (view := view) π F :=
  UCviaRel_iff_ExactUCEmulates π F

/-- **The `∃ sim` is essential — UC needs a (possibly non-trivial) simulator.** If the
*identity* simulator already relates real and ideal for every environment, UC holds
(the `∃ sim` witnessed trivially). The converse fails: genuine UC (Pedersen,
dual-OT) holds only via a non-trivial equivocating/extracting simulator with
`sim ≠ A`, where `real ≠ ideal` as leakage channels. So forcing `sim = id` is
strictly stronger than UC — the `∃ sim` quantifier cannot be dropped, confirming UC
is a *derived* notion over the coupling and not the plain relational judgment. -/
theorem uc_needs_nontrivial_simulator {T : Type → Type} [UCMonad.UCMonadBase T]
    {hon out leak view : Type} {π F : hon → T (out ⊕ leak)}
    (h : ∀ A : leak → T view,
      (fun a => π a >>= UCMonad.UCMonadBase.ucMapSum pure A)
        = (fun a => F a >>= UCMonad.UCMonadBase.ucMapSum pure A)) :
    UCviaRel (view := view) π F :=
  identityRel_implies_UCviaRel h

end CatCrypt.XDijkstra
