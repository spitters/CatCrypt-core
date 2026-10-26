/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Std.WP
public import CatCryptCore.XDijkstra.XPredCore

@[expose] public section
set_option autoImplicit false

/-!
# The toolchain's `WPMonad` class and `XCoreWP` at the trivial grade

The toolchain's program logic `Std.WP` (the Loom framework, `loom2`, as it entered
core) observes a monad `m` by a class `WPMonad m Pred EPred` whose field
`toWP α : WP (m α) α Pred EPred` carries, for each program `c : m α`, a monotone
transformer `wpTrans c : PredTrans Pred EPred α` over assertion types that are
complete lattices in the order `⊑` of `Lean.Order`, with the laws
`post x ⊑ wp (pure x) post epost` and
`wp x (fun a => wp (f a) post epost) epost ⊑ wp (x >>= f) post epost`. The class
`XCoreWP m Pred EPred G` observes `m` by graded transformers `XCorePT` over
assertion types ordered by `≤`, with monotonicity a field of the transformer
and the laws of `pure` and `bind` (as equalities) in `LawfulXCoreWP`.

The two orders are related by the class `LERelCompat`: `≤` and `⊑` agree. It
holds for `Prop` (both are implication) and pointwise for function types; for
an assertion type that carries only `⊑` (such as `EStack⟨⟩`), `relLE` is the
order `≤ := ⊑` and `relLE_compat` its compatibility.

## Main definitions

* `LERelCompat`, `relLE`: agreement of `≤` with `⊑`.
* `XCoreWP.ofWPMonad`: the observation of a `WPMonad` instance as an `XCoreWP`
  at grade type `Unit`.
* `XCoreWP.LowerLaws`: the transformers of an `XCoreWP` bound the return and
  bind transformers from above; these are the laws of `WPMonad`.
* `XCoreWP.toWPMonadOfLe`: a `WPMonad` instance from an `XCoreWP` of a lawful
  monad satisfying `LowerLaws`, at any grade type (the grade is forgotten);
  `XCoreWP.toWPMonad` the same from `LawfulXCoreWP`.

## Main statements

* `xcore_wp_eq_wp`, `wp_eq_xcore_wp`: the weakest preconditions agree under
  either construction.
* `triple_iff_xcoreTriple`, `xcoreTriple_iff_triple`: the triples agree under
  either construction.
* `lowerLaws_ofWPMonad`: `ofWPMonad` satisfies `LowerLaws`;
  `lawfulXCoreWP_ofWPMonad`: `ofWPMonad` is lawful when the laws of `WPMonad`
  hold with equality.
* `toWPMonad_ofWPMonad_wpTrans`, `ofWPMonad_toWPMonad_apply`: the two
  constructions are mutually inverse on weakest preconditions.

## The laws that differ

The laws of `WPMonad` for `pure` and `bind` are lower bounds (`⊑`), and
`LawfulXCoreWP` states them as equalities. A `WPMonad` instance therefore gives
an `XCoreWP` that satisfies `LowerLaws`, and an instance of `LawfulXCoreWP`
exactly when both inequalities are equalities. Monotonicity corresponds exactly.
-/

namespace CatCrypt.StdWPBridge

open Lean.Order Std.WP CatCrypt.XDijkstra

universe u v w w' g

/-! ## Agreement of `≤` with `⊑` -/

/-- The order `≤` of `α` is the order `⊑` of `Lean.Order`. -/
class LERelCompat (α : Type u) [LE α] [Lean.Order.PartialOrder α] : Prop where
  /-- `≤` and `⊑` agree. -/
  le_iff_rel : ∀ a b : α, a ≤ b ↔ a ⊑ b

/-- On `Prop` both orders are implication. -/
instance LERelCompat.instProp : LERelCompat Prop := ⟨fun _ _ => Iff.rfl⟩

/-- Both orders on a function type are pointwise. -/
instance LERelCompat.instPi {σ : Type u} {β : Type v} [LE β] [Lean.Order.PartialOrder β]
    [LERelCompat β] : LERelCompat (σ → β) :=
  ⟨fun _ _ => ⟨fun h x => (LERelCompat.le_iff_rel _ _).1 (h x),
    fun h x => (LERelCompat.le_iff_rel _ _).2 (h x)⟩⟩

/-- The order `≤ := ⊑` on a `Lean.Order` partial order. -/
@[reducible] def relLE (α : Type u) [Lean.Order.PartialOrder α] : LE α := ⟨PartialOrder.rel⟩

/-- `relLE` agrees with `⊑`. -/
theorem relLE_compat (α : Type u) [Lean.Order.PartialOrder α] :
    @LERelCompat α (relLE α) _ :=
  @LERelCompat.mk α (relLE α) _ fun _ _ => Iff.rfl

/-! ## The laws of `WPMonad` stated for an `XCoreWP` -/

/-- The transformers of an `XCoreWP` of `m` bound the return and bind
transformers from above: the laws of `WPMonad` for `pure` and `bind`. -/
structure XCoreWP.LowerLaws (m : Type u → Type v) {Pred : Type w} {EPred : Type w'}
    {G : Type g} [Monad m] [LE Pred] [LE EPred] [XCoreWP m Pred EPred G] : Prop where
  /-- The weakest precondition of `pure a` is above the postcondition at `a`. -/
  pure_le {α : Type u} (a : α) (post : α → Pred) (epost : EPred) :
    post a ≤ (XCoreWP.wp (pure a : m α) : XCorePT Pred EPred G α).apply post epost
  /-- The weakest precondition of `c >>= f` is above the bind of the weakest
  preconditions. -/
  bind_le {α β : Type u} (c : m α) (f : α → m β) (post : β → Pred) (epost : EPred) :
    ((XCoreWP.wp c : XCorePT Pred EPred G α).bind
        (fun a => (XCoreWP.wp (f a) : XCorePT Pred EPred G β))).apply post epost ≤
      (XCoreWP.wp (c >>= f) : XCorePT Pred EPred G β).apply post epost

/-! ## From `WPMonad` to `XCoreWP` -/

section OfWPMonad

variable (m : Type u → Type v) {Pred : Type w} {EPred : Type w'}
  [Monad m] [Assertion Pred] [Assertion EPred] [LE Pred] [LE EPred]
  [LERelCompat Pred] [LERelCompat EPred] [WPMonad m Pred EPred]

/-- The observation of a `WPMonad` instance as an `XCoreWP` at grade type `Unit`:
the transformer of `c` is the weakest precondition of `c`. -/
@[reducible] def XCoreWP.ofWPMonad : XCoreWP m Pred EPred Unit where
  wp c :=
    { apply := wp c
      grade := ()
      mono := fun hpost hepost =>
        (LERelCompat.le_iff_rel _ _).2
          (WP.wp_trans_monotone c _ _ _ _ ((LERelCompat.le_iff_rel _ _).1 hepost)
            (fun a => (LERelCompat.le_iff_rel _ _).1 (hpost a))) }

variable {m}

/-- The weakest precondition of `XCoreWP.ofWPMonad` is that of the `WPMonad`. -/
theorem xcore_wp_eq_wp {α : Type u} (c : m α) :
    (@XCoreWP.wp m Pred EPred Unit _ _ (XCoreWP.ofWPMonad m) α c).apply = wp c := rfl

/-- `XCoreWP.ofWPMonad` satisfies the laws of `WPMonad` as inequalities of
transformers. -/
theorem lowerLaws_ofWPMonad :
    @XCoreWP.LowerLaws m Pred EPred Unit _ _ _ (XCoreWP.ofWPMonad m) :=
  @XCoreWP.LowerLaws.mk m Pred EPred Unit _ _ _ (XCoreWP.ofWPMonad m)
    (fun a post epost => (LERelCompat.le_iff_rel _ _).2 (WPMonad.pure_le_wp_pure a post epost))
    (fun c f post epost =>
      (LERelCompat.le_iff_rel _ _).2 (WPMonad.bind_le_wp_bind c f post epost))

/-- `XCoreWP.ofWPMonad` is lawful when the laws of `WPMonad` for `pure` and `bind`
hold with equality. -/
theorem lawfulXCoreWP_ofWPMonad [Zero Unit]
    (hpure : ∀ {α : Type u} (a : α) (post : α → Pred) (epost : EPred),
      wp (pure a : m α) post epost = post a)
    (hbind : ∀ {α β : Type u} (c : m α) (f : α → m β) (post : β → Pred) (epost : EPred),
      wp (c >>= f) post epost = wp c (fun a => wp (f a) post epost) epost) :
    @LawfulXCoreWP m Pred EPred Unit _ _ _ _ (XCoreWP.ofWPMonad m) := by
  let _ := XCoreWP.ofWPMonad m
  exact ⟨fun a => XCorePT.ext (fun post epost => hpure a post epost) rfl,
    fun c f => XCorePT.ext (fun post epost => hbind c f post epost) rfl⟩

/-- A triple of the `WPMonad` is an `XCoreWP` triple of `XCoreWP.ofWPMonad`. -/
theorem triple_iff_xcoreTriple {α : Type u} {P : Pred} {c : m α}
    {post : α → Pred} {epost : EPred} :
    Triple c P post epost ↔
      @XCoreWP.Triple m Pred EPred Unit _ _ (XCoreWP.ofWPMonad m) α P c post epost :=
  Triple.iff.trans (LERelCompat.le_iff_rel _ _).symm

end OfWPMonad

/-! ## From `XCoreWP` to `WPMonad` -/

section ToWPMonad

variable (m : Type u → Type v) {Pred : Type w} {EPred : Type w'} {G : Type g}
  [Monad m] [LawfulMonad m] [Assertion Pred] [Assertion EPred] [LE Pred] [LE EPred]
  [LERelCompat Pred] [LERelCompat EPred] [XCoreWP m Pred EPred G]

/-- A `WPMonad` instance from an `XCoreWP` of a lawful monad satisfying the laws
of `WPMonad`. The grade is forgotten. -/
@[reducible] def XCoreWP.toWPMonadOfLe (h : XCoreWP.LowerLaws m (Pred := Pred)
    (EPred := EPred) (G := G)) : WPMonad m Pred EPred where
  toLawfulMonad := inferInstance
  toWP _ :=
    { wpTrans c := ⟨(XCoreWP.wp c : XCorePT Pred EPred G _).apply⟩
      wp_trans_monotone c := fun _ _ _ _ hepost hpost =>
        (LERelCompat.le_iff_rel _ _).1
          ((XCoreWP.wp c : XCorePT Pred EPred G _).mono
            (fun a => (LERelCompat.le_iff_rel _ _).2 (hpost a))
            ((LERelCompat.le_iff_rel _ _).2 hepost)) }
  pure_le_wp_pure a post epost := (LERelCompat.le_iff_rel _ _).1 (h.pure_le a post epost)
  bind_le_wp_bind c f post epost := (LERelCompat.le_iff_rel _ _).1 (h.bind_le c f post epost)

omit [LawfulMonad m] [Assertion EPred] [LERelCompat EPred] in
/-- A lawful `XCoreWP` satisfies the laws of `WPMonad`. -/
theorem lowerLaws_of_lawful [Zero G] [LawfulXCoreWP m Pred EPred] :
    XCoreWP.LowerLaws m (Pred := Pred) (EPred := EPred) (G := G) where
  pure_le a post epost := by
    rw [LawfulXCoreWP.wp_pure (G := G)]
    exact (LERelCompat.le_iff_rel _ _).2 PartialOrder.rel_refl
  bind_le c f post epost := by
    rw [LawfulXCoreWP.wp_bind (G := G) c f]
    exact (LERelCompat.le_iff_rel _ _).2 PartialOrder.rel_refl

/-- A `WPMonad` instance from a lawful `XCoreWP` of a lawful monad. -/
@[reducible] def XCoreWP.toWPMonad [Zero G] [LawfulXCoreWP m Pred EPred] :
    WPMonad m Pred EPred :=
  XCoreWP.toWPMonadOfLe m (lowerLaws_of_lawful m (G := G))

variable {m}

/-- The weakest precondition of `XCoreWP.toWPMonadOfLe` is that of the `XCoreWP`. -/
theorem wp_eq_xcore_wp (h : XCoreWP.LowerLaws m (Pred := Pred) (EPred := EPred) (G := G))
    {α : Type u} (c : m α) :
    ((XCoreWP.toWPMonadOfLe m h).toWP α).wp c =
      (XCoreWP.wp c : XCorePT Pred EPred G α).apply := rfl

/-- An `XCoreWP` triple is a triple of `XCoreWP.toWPMonadOfLe`. -/
theorem xcoreTriple_iff_triple
    (h : XCoreWP.LowerLaws m (Pred := Pred) (EPred := EPred) (G := G))
    {α : Type u} {P : Pred} {c : m α} {post : α → Pred} {epost : EPred} :
    XCoreWP.Triple (G := G) P c post epost ↔
      @Triple Pred EPred (m α) α _ _ c ((XCoreWP.toWPMonadOfLe m h).toWP α) P post epost :=
  (LERelCompat.le_iff_rel _ _).trans
    (@Triple.iff Pred EPred (m α) α _ _ ((XCoreWP.toWPMonadOfLe m h).toWP α) c P post
      epost).symm

end ToWPMonad

/-! ## Round trips -/

section RoundTrip

variable {m : Type u → Type v} {Pred : Type w} {EPred : Type w'}
  [Monad m] [Assertion Pred] [Assertion EPred] [LE Pred] [LE EPred]
  [LERelCompat Pred] [LERelCompat EPred]

/-- Observing a `WPMonad` instance through `XCoreWP.ofWPMonad` and back gives the
transformers of the instance. -/
theorem toWPMonad_ofWPMonad_wpTrans [inst : WPMonad m Pred EPred] {α : Type u} (c : m α) :
    ((@XCoreWP.toWPMonadOfLe m Pred EPred Unit _ inst.toLawfulMonad _ _ _ _ _ _
        (XCoreWP.ofWPMonad m) lowerLaws_ofWPMonad).toWP α).wpTrans c =
      (inst.toWP α).wpTrans c := rfl

/-- Building a `WPMonad` instance from an `XCoreWP` and observing it through
`XCoreWP.ofWPMonad` gives the weakest preconditions of the `XCoreWP`; the grade
becomes `()`. -/
theorem ofWPMonad_toWPMonad_apply [LawfulMonad m] {G : Type g} [XCoreWP m Pred EPred G]
    (h : XCoreWP.LowerLaws m (Pred := Pred) (EPred := EPred) (G := G)) {α : Type u} (c : m α) :
    (@XCoreWP.wp m Pred EPred Unit _ _
        (@XCoreWP.ofWPMonad m Pred EPred _ _ _ _ _ _ _ (XCoreWP.toWPMonadOfLe m h)) α c).apply =
      (XCoreWP.wp c : XCorePT Pred EPred G α).apply := rfl

end RoundTrip

/-! ## Transfer of a triple -/

section Example

/-- The order `≤ := ⊑` on the empty exception postcondition. -/
local instance : LE EStack⟨⟩ := relLE EStack⟨⟩

local instance : LERelCompat EStack⟨⟩ := relLE_compat EStack⟨⟩

/-- A triple of `pure 3` in `Id`, proved by `Std.WP.Triple.pure`, transfers to
the `XCoreWP` triple of `XCoreWP.ofWPMonad Id`. -/
theorem id_pure_xcoreTriple :
    @XCoreWP.Triple Id Prop EStack⟨⟩ Unit _ _ (XCoreWP.ofWPMonad Id) Nat
      True (pure 3) (fun n => n = 3) Lean.Order.bot :=
  triple_iff_xcoreTriple.1 (Triple.pure (m := Id) 3 (fun _ => rfl))

end Example

end CatCrypt.StdWPBridge
