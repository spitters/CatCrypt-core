/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.Basic
public import Mathlib.Logic.Equiv.Defs
public import CatCryptCore.XDijkstra.XPredCore

@[expose] public section
set_option autoImplicit false

/-!
# `XPostShape`: the extended-PostShape Dijkstra framework

This module defines an extended predicate-transformer ("extended PostShape")
framework that fuses four reasoning axes into a single transformer `XPredTrans`:

* **Graded** — a monoid grade `g : G` that accumulates (`g₁ + g₂`) under
  sequencing (cost / error-budget / interface accumulation);
* **Separation logic** — assertions live in an abstract carrier `Ω` equipped with
  a bunched product `∗`, so a frame rule holds;
* **Relational** — two programs are related via the product/self-composition,
  giving a relational Hoare judgment on the deterministic fragment;
* **Monad morphism** — a weakest-precondition transfer along an effect
  morphism `θ : m → n`, threading a `PostShape`-map on postconditions.

It extends Lean's `Std.Do` metatheory: `XPostShape` mirrors
`Std.Do.PostShape` (`pure | arg σ | except ε`) and adds a `graded G` layer;
`XAssertion`/`XPostCond`/`XPredTrans`/`XWP` mirror `Assertion`/`PostCond`/
`PredTrans`/`WP`, but every assertion is parameterized by the carrier `Ω`
(`Ω = Prop` for the plain instance, a BI carrier for separation logic). The core
works over abstract carriers: the four axis-laws, and the one obstacle
(monad-morphism lawfulness, below).

## Layering over the shape-free core

The shape is a layer over the transformer `XCorePT Pred EPred G α` of
`XPredCore.lean`, whose parameters are an assertion type, an exception-postcondition
type and a grade type, as in the predicate transformers of Lean's standard library
(`Pred`, `EPred`) with the grade as the additional parameter. A shape `ps` and a
carrier `Ω` compute the three parameters: `Pred := XAssertion ps Ω` ordered by
`XAssertion.le ps` (`XAssertion.preorder`), `EPred := XExceptConds ps Ω` ordered by
`XExceptConds.le ps` (`XExceptConds.preorder`), and `G := ps.Grade`.
`XPredTrans.equivCore` identifies `XPredTrans ps Ω α` with the core transformer at
these parameters; both round trips hold by `rfl`. Under it `xpure`, `xbind`, `xseq`
and `xprod` are the core's `ret`, `bind`, `seq` and `prod` (`xpure_toCore`,
`xbind_toCore`, `xseq_toCore`, `xprod_toCore`), `XPT` is `XCorePT.Triple`
(`xpt_iff_core`) and `XLocal` is `XCorePT.Local` (`xlocal_iff_core`). The axis laws
`xseq_triple`, `xwp_graded_bind`, `xtriple_grade_le`, `xframe`, `xpure_local`,
`xrel_seq` and `xwp_morphism` are instances of the core laws. The order and
separation structures on `XAssertion ps Ω` are definitions, local instances of this
file only.

## Design of the grade

A type-tag grade does not thread through `bind`: the weakest-precondition
observation never mentions the type index, so the accumulated grade is
unrecoverable from the transformer. The grade is therefore carried as a value
field `grade : ps.Grade`, where `ps.Grade` is the product of every `graded G`
layer's `G`. `xseq` (constant-continuation sequencing) adds grades at the value
level, `g₁ + g₂`.
-/

namespace CatCrypt.XDijkstra

universe u v

/-! ## 1. The extended postcondition shape

`XPostShape` mirrors `Std.Do.PostShape` and adds one constructor, `graded G`,
for a monoid grade layer. `G` is a bare `Type` in the constructor;
`[AddCommMonoid G] [Preorder G]` are required at the law sites, not here. -/

/-- The shape of the effect stack a monad reasons over, extended with a grade
layer. `pure` is the pure base; `arg σ` a state layer; `except ε` an exception
layer; `graded G` a **grade** layer whose monoid value accumulates under
sequencing. -/
inductive XPostShape : Type (u+1) where
  /-- Neither state, exceptions, nor grade. -/
  | pure : XPostShape
  /-- A state layer of type `σ`. -/
  | arg (σ : Type u) (ps : XPostShape) : XPostShape
  /-- An exception layer of type `ε`. -/
  | except (ε : Type u) (ps : XPostShape) : XPostShape
  /-- A **grade** layer of type `G` (a monoid at the law sites). -/
  | graded (G : Type u) (ps : XPostShape) : XPostShape

/-- The **grade carrier** of a shape: the product of every `graded G` layer's
`G` (and `PUnit` at the leaves). The transformer stores a value of this type;
for a concrete shape it reduces to a concrete product, so `AddCommMonoid`,
`Preorder`, etc. are found by ordinary instance resolution (`ℕ × PUnit`, …). At
an abstract shape the relevant instance is taken as a hypothesis. -/
@[reducible] def XPostShape.Grade : XPostShape.{u} → Type u
  | .pure => PUnit
  | .arg _ ps => ps.Grade
  | .except _ ps => ps.Grade
  | .graded G ps => G × ps.Grade

/-! ### Grade-monoid instances, structural on the shape

`ps.Grade` is a recursive `def`, which does **not** unfold during instance
resolution, so `Zero`/`Add` on it are provided **per constructor** here. Every
instance's head is `XPostShape.Grade`, so resolution unifies the shape argument
and descends — threading `0`/`+` through the grade product without touching the
recursive matcher, and needing no `Zero`/`Add` on `PUnit` (the leaf carries `⟨⟩`). -/

instance : Zero (XPostShape.pure.{u}).Grade := ⟨PUnit.unit⟩
instance {σ : Type u} {ps : XPostShape.{u}} [Zero ps.Grade] :
    Zero (XPostShape.arg σ ps).Grade := ⟨(0 : ps.Grade)⟩
instance {ε : Type u} {ps : XPostShape.{u}} [Zero ps.Grade] :
    Zero (XPostShape.except ε ps).Grade := ⟨(0 : ps.Grade)⟩
instance {G : Type u} {ps : XPostShape.{u}} [Zero G] [Zero ps.Grade] :
    Zero (XPostShape.graded G ps).Grade := ⟨((0 : G), (0 : ps.Grade))⟩

instance : Add (XPostShape.pure.{u}).Grade := ⟨fun _ _ => PUnit.unit⟩
instance {σ : Type u} {ps : XPostShape.{u}} [Add ps.Grade] :
    Add (XPostShape.arg σ ps).Grade := ⟨fun a b => (a + b : ps.Grade)⟩
instance {ε : Type u} {ps : XPostShape.{u}} [Add ps.Grade] :
    Add (XPostShape.except ε ps).Grade := ⟨fun a b => (a + b : ps.Grade)⟩
instance {G : Type u} {ps : XPostShape.{u}} [Add G] [Add ps.Grade] :
    Add (XPostShape.graded G ps).Grade := ⟨fun a b => (a.1 + b.1, a.2 + b.2)⟩

/-! ## 2. Carrier-parameterized assertions and postconditions

`XAssertion ps Ω` mirrors `Std.Do.Assertion`, but over an abstract assertion
carrier `Ω` (the assertion algebra: `Prop` for the plain instance, a BI
for separation logic). A state layer `.arg σ` prepends a `σ →`; the `.except`
and `.graded` layers leave the assertion unchanged (the exception barrels live in
`XExceptConds`, and the grade rides in the transformer, not the assertion). -/

/-- An assertion for shape `ps` valued in carrier `Ω`: a curried function from
the state stack of `ps` into `Ω`. -/
def XAssertion : XPostShape.{u} → Type u → Type u
  | .pure, Ω => Ω
  | .arg σ ps, Ω => σ → XAssertion ps Ω
  | .except _ ps, Ω => XAssertion ps Ω
  | .graded _ ps, Ω => XAssertion ps Ω

/-- One assertion barrel per `.except ε` layer, valued in `Ω`. Mirrors
`Std.Do.ExceptConds`. -/
def XExceptConds : XPostShape.{u} → Type u → Type u
  | .pure, _ => PUnit
  | .arg _ ps, Ω => XExceptConds ps Ω
  | .except ε ps, Ω => (ε → XAssertion ps Ω) × XExceptConds ps Ω
  | .graded _ ps, Ω => XExceptConds ps Ω

/-- A postcondition: a success assertion per return value plus the exception
barrels. Mirrors `Std.Do.PostCond`. -/
def XPostCond (α : Type u) (ps : XPostShape.{u}) (Ω : Type u) : Type u :=
  (α → XAssertion ps Ω) × XExceptConds ps Ω

/-! ### Entailment

Entailment on `Ω` is its `≤` (`Prop`'s `≤` is implication). It lifts pointwise
to assertions, exception-barrels, and postconditions. -/

variable {Ω : Type u}

/-- Pointwise entailment of assertions, lifting `≤` on the carrier `Ω`. -/
def XAssertion.le [LE Ω] : (ps : XPostShape.{u}) → XAssertion ps Ω → XAssertion ps Ω → Prop
  | .pure, P, Q => @LE.le Ω _ P Q
  | .arg σ ps, P, Q => ∀ s : σ, XAssertion.le ps (P s) (Q s)
  | .except _ ps, P, Q => XAssertion.le ps P Q
  | .graded _ ps, P, Q => XAssertion.le ps P Q

/-- Pointwise entailment of exception barrels. -/
def XExceptConds.le [LE Ω] : (ps : XPostShape.{u}) → XExceptConds ps Ω → XExceptConds ps Ω → Prop
  | .pure, _, _ => True
  | .arg _ ps, x, y => XExceptConds.le ps x y
  | .except _ ps, x, y => (∀ e, XAssertion.le ps (x.1 e) (y.1 e)) ∧ XExceptConds.le ps x.2 y.2
  | .graded _ ps, x, y => XExceptConds.le ps x y

/-- Entailment of postconditions: pointwise on the success assertion and on the
exception barrels. -/
def XPostCond.le [LE Ω] {α : Type u} {ps : XPostShape.{u}} (P Q : XPostCond α ps Ω) : Prop :=
  (∀ a, XAssertion.le ps (P.1 a) (Q.1 a)) ∧ XExceptConds.le ps P.2 Q.2

@[inherit_doc] scoped infix:25 " ⊢ₓ " => XPostCond.le

/-! ### Reflexivity and transitivity of assertion entailment (needed for `mono`) -/

theorem XAssertion.le_refl [Preorder Ω] :
    (ps : XPostShape.{u}) → (P : XAssertion ps Ω) → XAssertion.le ps P P
  | .pure, P => by show @LE.le Ω _ P P; exact _root_.le_refl _
  | .arg _ ps, P => fun s => XAssertion.le_refl ps (P s)
  | .except _ ps, P => XAssertion.le_refl ps P
  | .graded _ ps, P => XAssertion.le_refl ps P

theorem XAssertion.le_trans [Preorder Ω] :
    (ps : XPostShape.{u}) → {P Q R : XAssertion ps Ω} →
      XAssertion.le ps P Q → XAssertion.le ps Q R → XAssertion.le ps P R
  | .pure, P, _, R, hpq, hqr => by
      show @LE.le Ω _ P R; exact _root_.le_trans hpq hqr
  | .arg _ ps, _, _, _, hpq, hqr => fun s => XAssertion.le_trans ps (hpq s) (hqr s)
  | .except _ ps, _, _, _, hpq, hqr => XAssertion.le_trans ps hpq hqr
  | .graded _ ps, _, _, _, hpq, hqr => XAssertion.le_trans ps hpq hqr

/-- Reflexivity of exception-barrel entailment. -/
theorem XExceptConds.le_refl [Preorder Ω] :
    (ps : XPostShape.{u}) → (x : XExceptConds ps Ω) → XExceptConds.le ps x x
  | .pure, _ => trivial
  | .arg _ ps, x => XExceptConds.le_refl ps x
  | .except _ ps, x => ⟨fun e => XAssertion.le_refl ps (x.1 e), XExceptConds.le_refl ps x.2⟩
  | .graded _ ps, x => XExceptConds.le_refl ps x

theorem XPostCond.le_refl [Preorder Ω] {α : Type u} {ps : XPostShape.{u}}
    (Q : XPostCond α ps Ω) : Q ⊢ₓ Q :=
  ⟨fun a => XAssertion.le_refl ps (Q.1 a), XExceptConds.le_refl ps Q.2⟩

/-- Transitivity of exception-barrel entailment. -/
theorem XExceptConds.le_trans [Preorder Ω] :
    (ps : XPostShape.{u}) → {x y z : XExceptConds ps Ω} →
      XExceptConds.le ps x y → XExceptConds.le ps y z → XExceptConds.le ps x z
  | .pure, _, _, _, _, _ => trivial
  | .arg _ ps, _, _, _, hxy, hyz => XExceptConds.le_trans ps hxy hyz
  | .except _ ps, _, _, _, hxy, hyz =>
      ⟨fun e => XAssertion.le_trans ps (hxy.1 e) (hyz.1 e),
        XExceptConds.le_trans ps hxy.2 hyz.2⟩
  | .graded _ ps, _, _, _, hxy, hyz => XExceptConds.le_trans ps hxy hyz

/-! ### The shape's assertion types as preorders

The core transformer `XCorePT` takes its assertion and exception-postcondition
types with a `≤`. For a shape these are `XAssertion ps Ω` and `XExceptConds ps Ω`
under pointwise entailment. The two preorders are definitions, made local
instances of this file. -/

/-- The assertions of a shape, preordered by pointwise entailment. -/
@[reducible] def XAssertion.preorder [Preorder Ω] (ps : XPostShape.{u}) :
    Preorder (XAssertion ps Ω) where
  le := XAssertion.le ps
  le_refl := XAssertion.le_refl ps
  le_trans _ _ _ := XAssertion.le_trans ps

/-- The exception barrels of a shape, preordered by pointwise entailment. -/
@[reducible] def XExceptConds.preorder [Preorder Ω] (ps : XPostShape.{u}) :
    Preorder (XExceptConds ps Ω) where
  le := XExceptConds.le ps
  le_refl := XExceptConds.le_refl ps
  le_trans _ _ _ := XExceptConds.le_trans ps

attribute [local instance] XAssertion.preorder XExceptConds.preorder

/-! ## 3. The extended predicate transformer

`XPredTrans ps Ω α` mirrors `Std.Do.PredTrans`, plus a **grade** value field. It
carries:

* `apply` — the weakest-precondition map `XPostCond α ps Ω → XAssertion ps Ω`;
* `grade : ps.Grade` — the accumulated grade **value** (per the design note: a
  value, so it threads through sequencing);
* `mono` — monotonicity: a stronger postcondition yields a stronger precondition.
-/

variable [Preorder Ω]

/-- The extended predicate transformer: a monotone WP map carrying a grade value.
-/
structure XPredTrans (ps : XPostShape.{u}) (Ω : Type u) [LE Ω] (α : Type u) : Type u where
  /-- The weakest-precondition map. -/
  apply : XPostCond α ps Ω → XAssertion ps Ω
  /-- The accumulated grade value. -/
  grade : ps.Grade
  /-- A stronger postcondition yields a stronger precondition. -/
  mono : ∀ {Q Q' : XPostCond α ps Ω}, Q ⊢ₓ Q' → XAssertion.le ps (apply Q) (apply Q')

/-- **Extended return.** Grade `0`; `apply Q := Q.1 a`. -/
def xpure {ps : XPostShape.{u}} [Zero ps.Grade] {α : Type u} (a : α) :
    XPredTrans ps Ω α where
  apply Q := Q.1 a
  grade := 0
  mono h := h.1 a

/-- **Monadic bind.** Standard continuation-monad composition of the WP maps.
Its grade is the **head** grade `x.grade`: a general value-dependent continuation
`f` has no single static grade to add, so `bind` cannot accumulate additively (see
the module note and `xseq`). -/
def xbind {ps : XPostShape.{u}} {α β : Type u}
    (x : XPredTrans ps Ω α) (f : α → XPredTrans ps Ω β) : XPredTrans ps Ω β where
  apply Q := x.apply (fun a => (f a).apply Q, Q.2)
  grade := x.grade
  mono h := x.mono ⟨fun a => (f a).mono h, h.2⟩

instance instMonad {ps : XPostShape.{u}} [Zero ps.Grade] : Monad (XPredTrans ps Ω) where
  pure := xpure
  bind := xbind

@[simp] theorem xpure_apply {ps : XPostShape.{u}} [Zero ps.Grade] {α : Type u}
    (a : α) (Q : XPostCond α ps Ω) : (xpure (Ω := Ω) a).apply Q = Q.1 a := rfl

@[simp] theorem xbind_apply {ps : XPostShape.{u}} {α β : Type u}
    (x : XPredTrans ps Ω α) (f : α → XPredTrans ps Ω β) (Q : XPostCond β ps Ω) :
    (xbind x f).apply Q = x.apply (fun a => (f a).apply Q, Q.2) := rfl

/-! ### Monad laws at the `apply` level

`LawfulMonad (XPredTrans ps Ω)` does not hold as stated: the obstruction is the
grade field. Left-identity `pure a >>= f = f a` demands equal grades on both
sides: `(xbind (xpure a) f).grade = (xpure a).grade = 0`, whereas `(f a).grade`
is an arbitrary value that `bind` cannot read (`f`'s grade depends on the runtime
`a`, unavailable to the `Monad`-fixed `bind`). A value-graded transformer is a
lawful monad only after forgetting the grade; the value-graded and lawful-monad
requirements are jointly unsatisfiable. Additive grade accumulation is captured
by `xseq` (constant continuation, where the continuation grade is a single
value), not by the value-dependent `bind`.

The monad laws hold for the semantic `apply` component (below), which is what
`XWP` and every Hoare triple observe; the grade is threaded by `xseq`. -/

theorem xbind_pure_apply {ps : XPostShape.{u}} [Zero ps.Grade] {α β : Type u}
    (a : α) (f : α → XPredTrans ps Ω β) (Q : XPostCond β ps Ω) :
    (xbind (xpure a) f).apply Q = (f a).apply Q := rfl

theorem xpure_bind_apply {ps : XPostShape.{u}} [Zero ps.Grade] {α : Type u}
    (x : XPredTrans ps Ω α) (Q : XPostCond α ps Ω) :
    (xbind x (fun a => xpure a)).apply Q = x.apply Q := rfl

theorem xbind_assoc_apply {ps : XPostShape.{u}} {α β γ : Type u}
    (x : XPredTrans ps Ω α) (f : α → XPredTrans ps Ω β) (g : β → XPredTrans ps Ω γ)
    (Q : XPostCond γ ps Ω) :
    (xbind (xbind x f) g).apply Q = (xbind x (fun a => xbind (f a) g)).apply Q := rfl

/-! ### Graded sequencing (`xseq`): grades add as values

`xseq x y` sequences a `g₁`-transformer with a constant `g₂`-continuation,
producing a transformer at grade `g₁ + g₂` — the value-level accumulation
`gbind`/`seq` deliver. The grade threads here, unlike `xbind`, whose
value-dependent continuation forbids a static sum. -/

/-- **Graded sequencing.** Same WP composition as a constant-continuation `bind`,
but the grade is the **sum** `x.grade + y.grade`. -/
def xseq {ps : XPostShape.{u}} [Add ps.Grade] {α β : Type u}
    (x : XPredTrans ps Ω α) (y : XPredTrans ps Ω β) : XPredTrans ps Ω β where
  apply Q := x.apply (fun _ => y.apply Q, Q.2)
  grade := x.grade + y.grade
  mono h := x.mono ⟨fun _ => y.mono h, h.2⟩

@[simp] theorem xseq_apply {ps : XPostShape.{u}} [Add ps.Grade] {α β : Type u}
    (x : XPredTrans ps Ω α) (y : XPredTrans ps Ω β) (Q : XPostCond β ps Ω) :
    (xseq x y).apply Q = x.apply (fun _ => y.apply Q, Q.2) := rfl

@[simp] theorem xseq_grade {ps : XPostShape.{u}} [Add ps.Grade] {α β : Type u}
    (x : XPredTrans ps Ω α) (y : XPredTrans ps Ω β) :
    (xseq x y).grade = x.grade + y.grade := rfl

/-! ### The transformer as a core transformer

`XPredTrans ps Ω α` is the core transformer `XCorePT` at `Pred := XAssertion ps Ω`,
`EPred := XExceptConds ps Ω`, `G := ps.Grade`: the conversion curries the
postcondition pair. Return, bind and sequencing correspond definitionally. -/

/-- The core transformer of an extended transformer: `apply` curried over the
success assertion and the exception barrels. -/
def XPredTrans.toCore {ps : XPostShape.{u}} {α : Type u} (t : XPredTrans ps Ω α) :
    XCorePT (XAssertion ps Ω) (XExceptConds ps Ω) ps.Grade α where
  apply post epost := t.apply (post, epost)
  grade := t.grade
  mono h he := t.mono ⟨h, he⟩

/-- The extended transformer of a core transformer at the shape's parameters. -/
def XPredTrans.ofCore {ps : XPostShape.{u}} {α : Type u}
    (t : XCorePT (XAssertion ps Ω) (XExceptConds ps Ω) ps.Grade α) : XPredTrans ps Ω α where
  apply Q := t.apply Q.1 Q.2
  grade := t.grade
  mono h := t.mono h.1 h.2

@[simp] theorem XPredTrans.ofCore_toCore {ps : XPostShape.{u}} {α : Type u}
    (t : XPredTrans ps Ω α) : XPredTrans.ofCore t.toCore = t := rfl

@[simp] theorem XPredTrans.toCore_ofCore {ps : XPostShape.{u}} {α : Type u}
    (t : XCorePT (XAssertion ps Ω) (XExceptConds ps Ω) ps.Grade α) :
    (XPredTrans.ofCore t).toCore = t := rfl

/-- `XPredTrans ps Ω α` is the core transformer at the parameters computed from
the shape. -/
def XPredTrans.equivCore (ps : XPostShape.{u}) (Ω : Type u) [Preorder Ω] (α : Type u) :
    XPredTrans ps Ω α ≃ XCorePT (XAssertion ps Ω) (XExceptConds ps Ω) ps.Grade α where
  toFun := XPredTrans.toCore
  invFun := XPredTrans.ofCore
  left_inv _ := rfl
  right_inv _ := rfl

/-- `xpure` is the core return. -/
theorem xpure_toCore {ps : XPostShape.{u}} [Zero ps.Grade] {α : Type u} (a : α) :
    (xpure (Ω := Ω) (ps := ps) a).toCore = XCorePT.ret a := rfl

/-- `xbind` is the core bind. -/
theorem xbind_toCore {ps : XPostShape.{u}} {α β : Type u}
    (x : XPredTrans ps Ω α) (f : α → XPredTrans ps Ω β) :
    (xbind x f).toCore = x.toCore.bind (fun a => (f a).toCore) := rfl

/-- `xseq` is the core sequencing. -/
theorem xseq_toCore {ps : XPostShape.{u}} [Add ps.Grade] {α β : Type u}
    (x : XPredTrans ps Ω α) (y : XPredTrans ps Ω β) :
    (xseq x y).toCore = x.toCore.seq y.toCore := rfl

/-! ## 4. The effect observation `XWP` and Hoare triples

`XWP m ps Ω` mirrors `Std.Do.WP`: it observes a program `x : m α` as an extended
predicate transformer. `XPT` is the transformer-level Hoare triple `P ⊢ t.apply Q`
(the semantic core, on which every axis-law is stated); `XTriple` lifts it to a
program via `XWP.xwp`. -/

/-- The extended weakest-precondition observation of an effectful monad `m`. -/
class XWP (m : Type u → Type v) (ps : XPostShape.{u}) (Ω : Type u) [LE Ω] where
  /-- Interpret a program as an extended predicate transformer. -/
  xwp {α : Type u} : m α → XPredTrans ps Ω α

/-- **Transformer-level Hoare triple.** The precondition `P` entails the weakest
precondition of `t` at `Q`. Every axis-law below is phrased on `XPT`. -/
def XPT {ps : XPostShape.{u}} {α : Type u} (P : XAssertion ps Ω)
    (t : XPredTrans ps Ω α) (Q : XPostCond α ps Ω) : Prop :=
  XAssertion.le ps P (t.apply Q)

/-- **Program-level Hoare triple** `⦃P⦄ x ⦃Q⦄`, via the `XWP` observation. -/
def XTriple {m : Type u → Type v} {ps : XPostShape.{u}} {α : Type u}
    [XWP m ps Ω] (P : XAssertion ps Ω) (x : m α) (Q : XPostCond α ps Ω) : Prop :=
  XPT P (XWP.xwp x) Q

/-- The transformer-level triple is the core triple of the core transformer. -/
theorem xpt_iff_core {ps : XPostShape.{u}} {α : Type u} (P : XAssertion ps Ω)
    (t : XPredTrans ps Ω α) (Q : XPostCond α ps Ω) :
    XPT P t Q ↔ XCorePT.Triple P t.toCore Q.1 Q.2 := Iff.rfl

/-! ## 5. Axis-law I — grade: sequencing accumulates the grade

`xseq_triple` is Hoare composition with an intermediate assertion `R`, whose
conclusion grade is the sum `x.grade + y.grade` (`xseq_grade`): cost/budget
composes additively. `xtriple_grade_le` is the budget residual — sequencing two
sub-budget steps stays within the summed budget, using `add_le_add` on the
ordered grade monoid. -/

/-- **Graded sequencing rule (grades add).** From `{P} x {_ ↦ R}` and `{R} y {Q}`
obtain `{P} (xseq x y) {Q}`; the resulting transformer's grade is `x.grade +
y.grade` (`xseq_grade`). Post-strengthening inside `x` uses `x.mono` — exactly
where bundled monotonicity is needed. -/
theorem xseq_triple {ps : XPostShape.{u}} [Add ps.Grade] {α β : Type u}
    {P R : XAssertion ps Ω} {x : XPredTrans ps Ω α} {y : XPredTrans ps Ω β}
    {Q : XPostCond β ps Ω}
    (h₁ : XPT P x (fun _ => R, Q.2)) (h₂ : XPT R y Q) :
    XPT P (xseq x y) Q :=
  XCorePT.seq_triple (s := x.toCore) (t := y.toCore) h₁ h₂

/-- **The grade accumulates to `g₁ + g₂`.** At a `.graded G ps'` shape, the head
grade of `xseq x y` is the sum of the two head grades. -/
@[defeq] theorem xwp_graded_bind {G : Type u} {ps' : XPostShape.{u}} [Add G] [Add ps'.Grade]
    {α β : Type u}
    (x : XPredTrans (.graded G ps') Ω α) (y : XPredTrans (.graded G ps') Ω β) :
    (xseq x y).grade.1 = x.grade.1 + y.grade.1 :=
  XCorePT.seq_grade (x.toCore.mapGrade Prod.fst) (y.toCore.mapGrade Prod.fst)

/-- **Budget residual.** If two sequenced steps each stay within a sub-budget
(`x.grade.1 ≤ b₁`, `y.grade.1 ≤ b₂`) then their composition stays within the
summed budget `b₁ + b₂`. Uses `add_le_add` on the ordered grade monoid `G`. -/
theorem xtriple_grade_le {G : Type u} {ps' : XPostShape.{u}}
    [AddCommMonoid G] [Preorder G] [IsOrderedAddMonoid G]
    [Add ps'.Grade] {α β : Type u}
    (x : XPredTrans (.graded G ps') Ω α) (y : XPredTrans (.graded G ps') Ω β)
    {b₁ b₂ : G} (h₁ : x.grade.1 ≤ b₁) (h₂ : y.grade.1 ≤ b₂) :
    (xseq x y).grade.1 ≤ b₁ + b₂ :=
  XCorePT.seq_grade_le (x.toCore.mapGrade Prod.fst) (y.toCore.mapGrade Prod.fst) h₁ h₂

/-! ## 6. Axis-law II — separation logic: the frame rule

A minimal bunched-implication interface `XBI Ω` equips the carrier with a
separating product `∗` (`sep`), a unit (`emp`), and the one law the frame rule
needs: `∗` is monotone in its left argument. (A full BI adds
associativity/commutativity and the magic-wand adjunction; the frame rule needs
only monotonicity, so the interface is kept minimal.) `∗` lifts pointwise to
assertions; the frame rule holds for local transformers (`XLocal`) — those whose
WP absorbs a framed resource. -/

/-- A minimal bunched-implication carrier: a separating product `∗` monotone in
its left argument, plus a unit. Entailment is the ambient `≤`. -/
class XBI (Ω : Type u) [Preorder Ω] where
  /-- The separating conjunction `∗`. -/
  sep : Ω → Ω → Ω
  /-- The separation-logic unit. -/
  emp : Ω
  /-- `∗` is monotone in its left argument — the property the frame rule needs. -/
  sep_mono_left : ∀ {a b : Ω} (r : Ω), a ≤ b → sep a r ≤ sep b r

/-- Lift the separating product pointwise to an assertion, framing a resource `R`
across the state stack. -/
def XAssertion.sep [XBI Ω] :
    (ps : XPostShape.{u}) → XAssertion ps Ω → XAssertion ps Ω → XAssertion ps Ω
  | .pure, P, R => @XBI.sep Ω _ _ P R
  | .arg _σ ps, P, R => fun s => XAssertion.sep ps (P s) (R s)
  | .except _ ps, P, R => XAssertion.sep ps P R
  | .graded _ ps, P, R => XAssertion.sep ps P R

/-- `∗` on assertions is monotone in its left argument, lifting `XBI.sep_mono_left`.
-/
theorem XAssertion.sep_mono [XBI Ω] :
    (ps : XPostShape.{u}) → {P P' : XAssertion ps Ω} → (R : XAssertion ps Ω) →
      XAssertion.le ps P P' → XAssertion.le ps (XAssertion.sep ps P R) (XAssertion.sep ps P' R)
  | .pure, _, _, R, h => @XBI.sep_mono_left Ω _ _ _ _ R h
  | .arg _ ps, _, _, R, h => fun s => XAssertion.sep_mono ps (R s) (h s)
  | .except _ ps, _, _, R, h => XAssertion.sep_mono ps R h
  | .graded _ ps, _, _, R, h => XAssertion.sep_mono ps R h

/-- The assertions of a shape carry the core's separating product: the pointwise
lift of `∗`. A definition, made a local instance of this file. -/
@[reducible] def XAssertion.coreSep [XBI Ω] (ps : XPostShape.{u}) :
    XCoreSep (XAssertion ps Ω) where
  sep := XAssertion.sep ps
  sep_mono_left R h := XAssertion.sep_mono ps R h

attribute [local instance] XAssertion.coreSep

/-- Frame a resource `R` across the success barrels of a postcondition. -/
def XPostCond.frameSep [XBI Ω] {α : Type u} {ps : XPostShape.{u}}
    (Q : XPostCond α ps Ω) (R : XAssertion ps Ω) : XPostCond α ps Ω :=
  (fun a => XAssertion.sep ps (Q.1 a) R, Q.2)

/-- **Locality** (the frame property of a transformer): its weakest precondition
absorbs a framed resource. Every axis-law's frame rule holds for local
transformers; `xpure` is local (`xpure_local`). -/
def XLocal [XBI Ω] {α : Type u} {ps : XPostShape.{u}} (t : XPredTrans ps Ω α) : Prop :=
  ∀ (Q : XPostCond α ps Ω) (R : XAssertion ps Ω),
    XAssertion.le ps (XAssertion.sep ps (t.apply Q) R) (t.apply (Q.frameSep R))

/-- Locality is the core's locality of the core transformer. -/
theorem xlocal_iff_core [XBI Ω] {α : Type u} {ps : XPostShape.{u}} (t : XPredTrans ps Ω α) :
    XLocal t ↔ t.toCore.Local :=
  ⟨fun h post epost R => h (post, epost) R, fun h Q R => h Q.1 Q.2 R⟩

/-- **The frame rule.** For a local transformer, `⦃P⦄ t ⦃Q⦄` gives
`⦃P ∗ R⦄ t ⦃Q ∗ R⦄`. The proof frames `R` onto the entailment `P ⊢ t.apply Q`
(via `sep_mono`), then absorbs it into the WP (via locality). -/
theorem xframe [XBI Ω] {α : Type u} {ps : XPostShape.{u}}
    {t : XPredTrans ps Ω α} (hloc : XLocal t) {P R : XAssertion ps Ω}
    {Q : XPostCond α ps Ω} (h : XPT P t Q) :
    XPT (XAssertion.sep ps P R) t (Q.frameSep R) :=
  XCorePT.frame ((xlocal_iff_core t).1 hloc) h

/-- `xpure` is local: its WP is `Q.1 a`, and framing commutes with it definitionally.
-/
theorem xpure_local [XBI Ω] {ps : XPostShape.{u}} [Zero ps.Grade] {α : Type u} (a : α) :
    XLocal (xpure (Ω := Ω) (ps := ps) a) :=
  (xlocal_iff_core _).2 (XCorePT.ret_local a)

/-! ## 7. Axis-law III — relational: the product / self-composition

Two programs on the same
effect are related via the product transformer `xprod t₁ t₂`, whose WP runs `t₁`
then `t₂` and pairs the results. A relational Hoare judgment is then a unary
triple over the product. The deterministic-coupling rule is `xrel_seq`. -/

/-- **The product transformer.** `xprod t₁ t₂` sequences the two transformers and
pairs their return values; its WP is `t₁`'s WP threaded through `t₂`'s WP. -/
def xprod {ps : XPostShape.{u}} {α β : Type u}
    (t₁ : XPredTrans ps Ω α) (t₂ : XPredTrans ps Ω β) : XPredTrans ps Ω (α × β) where
  apply Q := t₁.apply (fun a => t₂.apply (fun b => Q.1 (a, b), Q.2), Q.2)
  grade := t₁.grade
  mono h := t₁.mono ⟨fun a => t₂.mono ⟨fun b => h.1 (a, b), h.2⟩, h.2⟩

@[simp] theorem xprod_apply {ps : XPostShape.{u}} {α β : Type u}
    (t₁ : XPredTrans ps Ω α) (t₂ : XPredTrans ps Ω β) (Q : XPostCond (α × β) ps Ω) :
    (xprod t₁ t₂).apply Q
      = t₁.apply (fun a => t₂.apply (fun b => Q.1 (a, b), Q.2), Q.2) := rfl

/-- `xprod` is the core product. -/
theorem xprod_toCore {ps : XPostShape.{u}} {α β : Type u}
    (t₁ : XPredTrans ps Ω α) (t₂ : XPredTrans ps Ω β) :
    (xprod t₁ t₂).toCore = t₁.toCore.prod t₂.toCore := rfl

/-- **The relational Hoare judgment.** For related inputs (`P`), the paired
outputs of `t₁` and `t₂` are related by `Ψ`. This is a **unary** triple over the
product transformer — the product *is* the relation. -/
def XRelTriple {ps : XPostShape.{u}} {α β : Type u}
    (P : XAssertion ps Ω) (t₁ : XPredTrans ps Ω α) (t₂ : XPredTrans ps Ω β)
    (Ψ : α × β → XAssertion ps Ω) (E : XExceptConds ps Ω) : Prop :=
  XPT P (xprod t₁ t₂) (Ψ, E)

/-- **The relational sequencing rule (deterministic coupling).** If `t₁` takes `P`
to an intermediate `Rmid a` and, for each `a`, `t₂` takes `Rmid a` to `Ψ (a, b)`,
then the product relates `t₁` and `t₂` from `P` to `Ψ`. Post-strengthening inside
`t₁` uses `t₁.mono`. -/
theorem xrel_seq {ps : XPostShape.{u}} {α β : Type u}
    {P : XAssertion ps Ω} {t₁ : XPredTrans ps Ω α} {t₂ : XPredTrans ps Ω β}
    {Rmid : α → XAssertion ps Ω} {Ψ : α × β → XAssertion ps Ω} {E : XExceptConds ps Ω}
    (h₁ : XPT P t₁ (Rmid, E))
    (h₂ : ∀ a, XPT (Rmid a) t₂ (fun b => Ψ (a, b), E)) :
    XRelTriple P t₁ t₂ Ψ E :=
  XCorePT.rel_seq (s := t₁.toCore) (t := t₂.toCore) h₁ h₂

/-! ## 8. Axis-law IV — monad morphism: WP transfer along `θ`

An effect morphism
`θ : m → n` transfers weakest preconditions. `XWPMorphism θ` bundles a
`PostShape`-map `postMap` on postconditions (`θ#`), a precondition map `preMap`
(both shapes may differ), and the **transfer law**
`xwp⟦θ x⟧ Q = preMap (xwp⟦x⟧ (θ# Q))`. The theorem `xwp_morphism` transports a
triple about `x` in `m` into a triple about `θ x` in `n`. -/

/-- A weakest-precondition **morphism** along an effect morphism `θ : m → n`:
a `PostShape`-map `postMap` on postconditions, a monotone precondition map
`preMap`, and the transfer law relating the two WP observations. -/
class XWPMorphism {m n : Type u → Type v} {psm psn : XPostShape.{u}}
    [XWP m psm Ω] [XWP n psn Ω] (θ : {α : Type u} → m α → n α) where
  /-- The `PostShape`-map `θ#` carrying an `n`-postcondition to an `m`-postcondition. -/
  postMap : {α : Type u} → XPostCond α psn Ω → XPostCond α psm Ω
  /-- The precondition map from the `m`-shape to the `n`-shape. -/
  preMap : XAssertion psm Ω → XAssertion psn Ω
  /-- `preMap` is monotone. -/
  preMap_mono : ∀ {A B : XAssertion psm Ω},
    XAssertion.le psm A B → XAssertion.le psn (preMap A) (preMap B)
  /-- **Transfer law:** `xwp⟦θ x⟧ Q = preMap (xwp⟦x⟧ (θ# Q))`. -/
  transfer : ∀ {α : Type u} (x : m α) (Q : XPostCond α psn Ω),
    (XWP.xwp (θ x)).apply Q = preMap ((XWP.xwp x).apply (postMap Q))

/-- **Morphism transfer of Hoare triples.** Given the morphism `θ`, a triple
`⦃P₀⦄ x ⦃θ# Q⦄` in `m` transports to `⦃preMap P₀⦄ θ x ⦃Q⦄` in `n`. The proof
rewrites the `n`-WP via the transfer law, then applies `preMap`'s monotonicity to
the `m`-triple. -/
theorem xwp_morphism {m n : Type u → Type v} {psm psn : XPostShape.{u}}
    [XWP m psm Ω] [XWP n psn Ω] {θ : {α : Type u} → m α → n α}
    [inst : XWPMorphism (Ω := Ω) (m := m) (n := n) (psm := psm) (psn := psn) θ]
    {α : Type u} (x : m α) {P₀ : XAssertion psm Ω} {Q : XPostCond α psn Ω}
    (h : XTriple (m := m) P₀ x (inst.postMap Q)) :
    XTriple (m := n) (inst.preMap P₀) (θ x) Q :=
  XCorePT.Triple.transfer (t := (XWP.xwp x).toCore) (t' := (XWP.xwp (θ x)).toCore)
    inst.preMap_mono (inst.transfer x Q) h

/-! ## 9. The transformer as its own effect (`XWP` for `XPredTrans`)

`XPredTrans ps Ω` observes itself via the identity — the canonical `XWP`
instance, used by the demos to exercise the triples and the morphism law. -/

/-- The identity `XWP`: a transformer observes itself. -/
instance instXWPSelf {ps : XPostShape.{u}} : XWP (XPredTrans ps Ω) ps Ω where
  xwp := id

@[simp] theorem xwp_self {ps : XPostShape.{u}} {α : Type u} (t : XPredTrans ps Ω α) :
    (XWP.xwp t : XPredTrans ps Ω α) = t := rfl

/-! ## 10. Worked demos — one per axis (carrier `Ω := Prop`)

Each demo exercises the fused core on the plain `Prop` carrier: a graded
two-step, a framed pure step, a related pair, and a morphism transfer. Together
they witness that the four axes are usable through one `XPredTrans`. -/

section Demos

/-- The plain assertion algebra: `∗ := ∧`, `emp := True`. Monotone in `∧`. -/
instance instXBIProp : XBI Prop where
  sep := And
  emp := True
  sep_mono_left := fun _r hab hb => ⟨hab hb.1, hb.2⟩

/-! ### Demo I (GRADED): two unit-cost steps sum to grade `2` -/

/-- A single unit-cost step at shape `.graded ℕ .pure`, grade `(1, ⟨⟩)`. -/
def stepCost1 : XPredTrans (.graded ℕ .pure) Prop Unit where
  apply Q := Q.1 ()
  grade := (1, ⟨⟩)
  mono h := h.1 ()

/-- **Graded demo.** Two unit-cost steps sequence via `xseq` into grade
`1 + 1 = 2` (`xwp_graded_bind`), and `xseq_triple` yields a triple through both
steps. -/
theorem demo_graded :
    (xseq stepCost1 stepCost1).grade.1 = 2
    ∧ XPT (ps := .graded ℕ .pure) True (xseq stepCost1 stepCost1) (fun _ => True, ⟨⟩) := by
  refine ⟨rfl, ?_⟩
  refine xseq_triple (Ω := Prop) (ps := .graded ℕ .pure) (R := True) ?_ ?_
  · exact fun _ => trivial
  · exact fun _ => trivial

/-! ### Demo II (SL / FRAME): frame a resource onto a pure step -/

/-- **Frame demo.** The trivially-true triple `⦃Q.1 a⦄ xpure a ⦃Q⦄` frames a
resource `R`: `⦃(Q.1 a) ∗ R⦄ xpure a ⦃Q ∗ R⦄`, via `xframe` and `xpure_local`. -/
theorem demo_frame (a : Nat) (R : Prop) (Q : XPostCond Nat .pure Prop) :
    XPT (ps := .pure) (XAssertion.sep .pure (Q.1 a) R)
      (xpure (Ω := Prop) (ps := .pure) a) (Q.frameSep R) :=
  xframe (xpure_local a) (XAssertion.le_refl .pure (Q.1 a))

/-! ### Demo III (RELATIONAL): relate two pure programs by the product -/

/-- **Relational demo.** Two pure programs returning `3` are related by the
diagonal `p.1 = p.2` through the product transformer, via `xrel_seq`. -/
theorem demo_relational :
    XRelTriple (ps := .pure) True
      (xpure (Ω := Prop) (ps := .pure) (3 : Nat))
      (xpure (Ω := Prop) (ps := .pure) (3 : Nat))
      (fun p => p.1 = p.2) ⟨⟩ :=
  xrel_seq (Ω := Prop) (ps := .pure) (Rmid := fun a => a = 3)
    (fun _ => rfl) (fun _ h => h)

/-! ### Demo IV (MORPHISM): the identity morphism transfers a triple -/

/-- The identity effect morphism on `XPredTrans ps Prop` is a WP morphism (all
maps identity, transfer by `rfl`). -/
instance instXWPMorphismId {ps : XPostShape.{0}} :
    XWPMorphism (Ω := Prop) (m := XPredTrans ps Prop) (n := XPredTrans ps Prop)
      (psm := ps) (psn := ps) (fun {_} t => t) where
  postMap := id
  preMap := id
  preMap_mono h := h
  transfer _ _ := rfl

/-- **Morphism demo.** Through the identity morphism, a self-triple on `t`
transports to a triple on `θ t = t` — a concrete use of `xwp_morphism`. -/
theorem demo_morphism {ps : XPostShape.{0}} (t : XPredTrans ps Prop Nat)
    (P : XAssertion ps Prop) (Q : XPostCond Nat ps Prop)
    (h : XTriple (m := XPredTrans ps Prop) P t Q) :
    XTriple (m := XPredTrans ps Prop) P ((fun {_} t => t) t) Q :=
  xwp_morphism (θ := fun {_} t => t) (P₀ := P) (Q := Q) t h

end Demos

end CatCrypt.XDijkstra
