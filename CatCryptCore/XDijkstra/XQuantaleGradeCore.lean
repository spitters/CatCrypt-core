/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ENNReal.Operations
public import Mathlib.Order.CompleteLattice.Lemmas
public import CatCryptCore.ForMathlib.GradeQuantale
public import CatCryptCore.XDijkstra.XPostShape

@[expose] public section

set_option autoImplicit false

/-!
# `XQuantaleGradeCore`: the XDijkstra grade over a quantale

The `.graded G` layer of `XPostShape` carries the grade as a monoid value: `xseq`
accumulates it as `g₁ + g₂`. The advantage grade is the Lawvere quantale
`([0, ∞], ≤, +, 0)`, a complete lattice and a commutative monoid, so it carries a
second grade operation: the lattice join `⊔` and the supremum `⨆` of a family.

This file states the two grade operations and their laws over the `GradeQuantale`
interface, and the transformer combinator for the join:

* `gmul := (+)`, sequential composition (the monoid product);
* `gjoin := (⊔)`, parallel or worst-case composition (the lattice join);
* `join_le_add : a ⊔ b ≤ a + b`, valid over every `GradeQuantale`;
* `quantale_distrib : a + (b ⊔ c) = (a + b) ⊔ (a + c)`, the distributive law, a
  field of the stronger class `GradeQuantaleJoin` and proved at `ℝ≥0∞` from
  `ENNReal.add_iSup`;
* `gmul_iSup_ennreal`, the distributive law over a family at `ℝ≥0∞`;
* `xpar`, the sibling of `xseq` whose head grade is `x.grade ⊔ y.grade`, with
  `xpar_grade_le_xseq` bounding it by the `xseq` grade.

The file depends on Mathlib, `GradeQuantale` and `XPostShape` only.

## Main results

* `join_le_add`, `gjoin_le_gmul`: the join of two grades is below their sum.
* `quantale_distrib`, `quantale_distrib_right`, `gmul_gjoin_ennreal`: addition distributes
  over joins and suprema at `ℝ≥0∞`.
* `xwp_graded_par`, `xpar_grade_le_xseq`: the join combinator `xpar` on transformers, and
  its grade is below the grade of the sequential composition.
-/

namespace CatCrypt.XDijkstra

open CatCrypt.Bridge
open scoped ENNReal

universe u

/-! ## 1. The quantale-graded grade: `gmul` (`+`), `gjoin` (`⊔`), and the laws

Over the `GradeQuantale` interface (a complete lattice + ordered commutative
monoid) the grade carries two operations: the monoid product `gmul` and the
lattice join `gjoin`. The join-below-sum law `join_le_add` needs only the interface.
The distributive law `quantale_distrib` needs the strictly stronger
`GradeQuantaleJoin` (the full Lawvere quantale), realized at `ℝ≥0∞`. -/

/-- **Sequential / advantage composition of grades** — the quantale monoid product.
This is the operation `xseq` threads (`ε₁ + ε₂`). -/
def gmul {V : Type*} [GradeQuantale V] (a b : V) : V := a + b

/-- **Parallel / worst-case composition of grades** — the quantale lattice join.
This is the grade of a composition in which one branch runs per input
(`ε₁ ⊔ ε₂`). -/
def gjoin {V : Type*} [GradeQuantale V] (a b : V) : V := a ⊔ b

/-- **The quantale fact `⊔ ≤ +`.** The worst-case join is bounded by the additive
product: `a ⊔ b ≤ a + b`. Both summands dominate their join (`le_add_right`,
`le_add_left`), so their join does too. The law holds over any `GradeQuantale`. -/
theorem join_le_add {V : Type*} [GradeQuantale V] (a b : V) : a ⊔ b ≤ a + b :=
  sup_le (GradeQuantale.le_add_right a b) (GradeQuantale.le_add_left a b)

/-- `gjoin` is below `gmul`: the parallel grade never exceeds the sequential one. -/
theorem gjoin_le_gmul {V : Type*} [GradeQuantale V] (a b : V) : gjoin a b ≤ gmul a b :=
  join_le_add a b

/-- Each member of a family is below the family join `⨆` — the `∀`-adversary
worst-case supremum as a native grade. -/
theorem le_gjoin_family {V : Type*} [GradeQuantale V] {ι : Sort*} (f : ι → V) (i : ι) :
    f i ≤ ⨆ j, f j :=
  le_iSup f i

/-! ### The distributive quantale (the full Lawvere law)

`GradeQuantale` provides the lattice and the ordered monoid but not the
distributive law `a + ⨆ = ⨆ (a + ·)`. The class `GradeQuantaleJoin` adds the binary
form of that law, under which bind-then-join equals join-of-binds; the instance at
`ℝ≥0∞` follows from `ENNReal.add_iSup`. -/

/-- A **distributive** grade quantale (the full Lawvere quantale): a `GradeQuantale`
in which `+` distributes over the lattice join. This is the law `GradeQuantale`
omits; it makes `gjoin` coherent with `gmul`. The instance is `ℝ≥0∞`.

The field is the **binary** distributive law (all in `V`'s universe). The
universe-polymorphic family form `a + ⨆ i, f i = ⨆ i, a + f i` cannot be a class
field (a `∀ {ι : Sort*}` field would pin a single class-level universe, not one per
use); it is provided at `ℝ≥0∞` directly as `gmul_iSup_ennreal`. -/
class GradeQuantaleJoin (V : Type*) extends GradeQuantale V where
  /-- `+` distributes over the binary join — the quantale law. -/
  protected add_sup : ∀ (a b c : V), a + (b ⊔ c) = (a + b) ⊔ (a + c)

/-- `ℝ≥0∞` is a distributive grade quantale — the Lawvere quantale
`([0, ∞], ≤, +, 0)`, with the distributive law from `ENNReal.add_iSup`. -/
noncomputable instance : GradeQuantaleJoin ℝ≥0∞ where
  add_sup a b c := by
    have h := ENNReal.add_iSup (a := a) (fun x : Bool => bif x then b else c)
    simpa only [iSup_bool_eq, Bool.cond_true, Bool.cond_false] using h

/-- **The quantale distributive law (binary `⊔`)**: `a + (b ⊔ c) = (a + b) ⊔ (a + c)`
— bind-then-join equals the join of the binds. The full Lawvere quantale law that
makes the join a coherent grade operation. -/
theorem quantale_distrib {V : Type*} [GradeQuantaleJoin V] (a b c : V) :
    a + (b ⊔ c) = (a + b) ⊔ (a + c) :=
  GradeQuantaleJoin.add_sup a b c

/-- **The quantale distributive law over a family (`⨆`), at the Lawvere quantale
`ℝ≥0∞`.** `+` on the left distributes over the `∀`-adversary supremum:
`a + ⨆ i, f i = ⨆ i, a + f i` (`ENNReal.add_iSup`). This is the `⨆`-form of
`quantale_distrib` — universe-polymorphic in the adversary index `ι`, hence a
standalone lemma rather than a class field. -/
theorem gmul_iSup_ennreal {ι : Sort*} [Nonempty ι] (a : ℝ≥0∞) (f : ι → ℝ≥0∞) :
    a + ⨆ i, f i = ⨆ i, a + f i :=
  ENNReal.add_iSup f

/-- The symmetric distributive law (right `⊔`): `(a ⊔ b) + c = (a + c) ⊔ (b + c)`. -/
theorem quantale_distrib_right {V : Type*} [GradeQuantaleJoin V] (a b c : V) :
    (a ⊔ b) + c = (a + c) ⊔ (b + c) := by
  rw [add_comm, quantale_distrib, add_comm c a, add_comm c b]

/-- At `ℝ≥0∞`, `gmul` is `+` and `gjoin` is `⊔`, both by definition, on the Lawvere
quantale `([0, ∞], ≤, +, 0)`. -/
theorem gmul_gjoin_ennreal (a b : ℝ≥0∞) : gmul a b = a + b ∧ gjoin a b = a ⊔ b :=
  ⟨rfl, rfl⟩

/-! ## 2. The join as a first-class transformer grade op (`xpar`)

`xseq` (`XPostShape`) combines the transformer grade by `+` under
`[Add ps.Grade]`. Here we give the join sibling: `Max`-instances on the recursive
grade carrier `ps.Grade` (mirroring the per-constructor `Zero`/`Add` instances),
and `xpar`, whose head grade is the quantale join `x.grade ⊔ y.grade`. -/

/-! ### Grade-join instances, structural on the shape

`ps.Grade` is a recursive `def` that does not unfold during instance resolution, so
`Max` on it is provided per constructor, exactly as `Add`/`Zero` are. Every head is
`XPostShape.Grade`, so resolution unifies the shape and descends. -/

instance : Max (XPostShape.pure.{u}).Grade := ⟨fun _ _ => PUnit.unit⟩
instance {σ : Type u} {ps : XPostShape.{u}} [Max ps.Grade] :
    Max (XPostShape.arg σ ps).Grade := ⟨fun a b => (a ⊔ b : ps.Grade)⟩
instance {ε : Type u} {ps : XPostShape.{u}} [Max ps.Grade] :
    Max (XPostShape.except ε ps).Grade := ⟨fun a b => (a ⊔ b : ps.Grade)⟩
instance {G : Type u} {ps : XPostShape.{u}} [Max G] [Max ps.Grade] :
    Max (XPostShape.graded G ps).Grade := ⟨fun a b => (a.1 ⊔ b.1, a.2 ⊔ b.2)⟩

variable {Ω : Type u} [Preorder Ω]

/-- **Parallel / branch sequencing.** The join sibling of `xseq`: the same WP
composition (both branches' preconditions threaded), but the grade is the quantale
**join** `x.grade ⊔ y.grade` — worst-case, not additive. Since `join_le_add`, `xpar`
is a grade-refinement of `xseq` (`xpar_grade_le_xseq`). -/
def xpar {ps : XPostShape.{u}} [Max ps.Grade] {α β : Type u}
    (x : XPredTrans ps Ω α) (y : XPredTrans ps Ω β) : XPredTrans ps Ω β where
  apply Q := x.apply (fun _ => y.apply Q, Q.2)
  grade := x.grade ⊔ y.grade
  mono h := x.mono ⟨fun _ => y.mono h, h.2⟩

@[simp] theorem xpar_apply {ps : XPostShape.{u}} [Max ps.Grade] {α β : Type u}
    (x : XPredTrans ps Ω α) (y : XPredTrans ps Ω β) (Q : XPostCond β ps Ω) :
    (xpar x y).apply Q = x.apply (fun _ => y.apply Q, Q.2) := rfl

@[simp] theorem xpar_grade {ps : XPostShape.{u}} [Max ps.Grade] {α β : Type u}
    (x : XPredTrans ps Ω α) (y : XPredTrans ps Ω β) :
    (xpar x y).grade = x.grade ⊔ y.grade := rfl

/-- **The grade joins to `g₁ ⊔ g₂`.** At a `.graded G ps'` shape, the head grade of
`xpar x y` is the join of the two head grades — the `xpar` analogue of
`xwp_graded_bind`. -/
theorem xwp_graded_par {G : Type u} {ps' : XPostShape.{u}} [Max G] [Max ps'.Grade]
    {α β : Type u}
    (x : XPredTrans (.graded G ps') Ω α) (y : XPredTrans (.graded G ps') Ω β) :
    (xpar x y).grade.1 = x.grade.1 ⊔ y.grade.1 := rfl

/-- **The parallel grade is within the sequential (`xseq`) budget.** At a
`.graded G ps'` shape over a grade quantale `G`, the `xpar` head grade
`g₁ ⊔ g₂` is `≤` the `xseq` head grade `g₁ + g₂` — a direct application of the
quantale law `join_le_add`. -/
theorem xpar_grade_le_xseq {G : Type u} [GradeQuantale G] {ps' : XPostShape.{u}}
    [Add ps'.Grade] [Max ps'.Grade] {α β : Type u}
    (x : XPredTrans (.graded G ps') Ω α) (y : XPredTrans (.graded G ps') Ω β) :
    (xpar x y).grade.1 ≤ (xseq x y).grade.1 :=
  join_le_add x.grade.1 y.grade.1

end CatCrypt.XDijkstra
