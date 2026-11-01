/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.Code

/-!
# Heterogeneous relational lifts along relations between codes

The heterogeneous lift `HFreeRel S R` relates the free monads of two polynomial functors `P` and
`Q` along a signature relation `S : SigRel P Q`, a relation between positions and a relation
between directions: two nodes are related when their positions are related and their
continuations are related at related directions. A relation `OpRel o₁ o₂` between two operation
codes of the same shape relates their fields by relations `S₁ → S₂ → Prop` and their direction
types by a relation; a relation `CodeRel c₁ c₂` between two codes relates their operations one
by one, and gives the signature relation `CodeRel.toSigRel` between their polynomial functors.

A relational lifting `RelLift m m'` of two monads relates computations `m α` and `m' β` along a
relation `α → β → Prop`, with a rule for `pure` and a rule for bind. Handlers `h` and `h'` of `P`
and `Q` into `m` and `m'` are related along `S` when they send related positions to computations
related by the direction relation; such handlers interpret `HFreeRel`-related programs by
`FreeM.liftM` to related computations (`HFreeRel.liftM_rel`).

## Main definitions

* `SigRel`, `HFreeRel` — signature relations and the heterogeneous lift;
* `OpRel`, `CodeRel`, `CodeRel.toSigRel`, `Code.HRel` — relations between codes of the same
  shape and the lift along them;
* `RelLift` — a relational lifting of two monads, with its `pure` and bind rules.

## Main results

* `hFreeRel_iff_freeRel` — over an identity signature relation the heterogeneous lift is
  `FreeRel`;
* `hFreeRel_pure_iff`, `hFreeRel_liftBind_iff`, `not_hFreeRel_pure_liftBind`,
  `not_hFreeRel_liftBind_pure` — inversion of the heterogeneous lift;
* `HFreeRel.mono`, `HFreeRel.bind` — monotonicity and compatibility with bind;
* `CodeRel.refl_isId`, `Code.hRel_refl_iff` — the reflexive relation of a code is an identity
  signature relation, and the lift along it is `Code.Rel`;
* `HFreeRel.liftM_rel` — related handlers interpret related programs to related computations.

Search words: parametricity, relational lift, relator, free monad, program tree, code,
heterogeneous relation, signature relation, relational handler, effect handler, relational
lifting of a monad, interpretation.
-/

set_option autoImplicit false

@[expose] public section

universe u v u' v' w w' x x'

namespace CatCrypt.Container

open PFunctor

variable {P : PFunctor.{u, v}} {α : Type w} {β : Type w'}

/-! ## Signature relations and the heterogeneous lift -/

/-- A relation between the signatures `P` and `Q`: a relation between their positions and a
relation between their directions. -/
structure SigRel (P : PFunctor.{u, v}) (Q : PFunctor.{u', v'}) where
  /-- The relation between positions. -/
  pos : P.A → Q.A → Prop
  /-- The relation between the directions at two positions. -/
  dir : ∀ a a', P.B a → Q.B a' → Prop

/-- A signature relation on `P` is an identity when it relates equal positions only and, at one
position, equal directions only. -/
structure SigRel.IsId {P : PFunctor.{u, v}} (S : SigRel P P) : Prop where
  /-- Positions are related exactly when they are equal. -/
  pos_iff : ∀ a a', S.pos a a' ↔ a = a'
  /-- Directions at one position are related exactly when they are equal. -/
  dir_iff : ∀ a (d d' : P.B a), S.dir a a d d' ↔ d = d'

/-- The heterogeneous relational lift of `R : α → β → Prop` along a signature relation `S`:
leaves with related results are related, and two nodes are related when their positions are
related and their continuations are related at related directions. -/
inductive HFreeRel {P : PFunctor.{u, v}} {Q : PFunctor.{u', v'}} (S : SigRel P Q)
    {α : Type w} {β : Type w'} (R : α → β → Prop) : P.FreeM α → Q.FreeM β → Prop where
  /-- Leaves with related results. -/
  | pure {a : α} {b : β} : R a b → HFreeRel S R (.pure a) (.pure b)
  /-- Nodes at related positions with continuations related at related directions. -/
  | liftBind {a : P.A} {a' : Q.A} {k : P.B a → P.FreeM α} {k' : Q.B a' → Q.FreeM β} :
      S.pos a a' → (∀ d d', S.dir a a' d d' → HFreeRel S R (k d) (k' d')) →
      HFreeRel S R (.liftBind a k) (.liftBind a' k')

section HFreeRel

variable {Q : PFunctor.{u', v'}} {S : SigRel P Q}

/-- Over an identity signature relation the heterogeneous lift is `FreeRel`. -/
theorem hFreeRel_iff_freeRel {S : SigRel P P} (hS : S.IsId) {R : α → β → Prop}
    {x : P.FreeM α} {y : P.FreeM β} : HFreeRel S R x y ↔ FreeRel P R x y := by
  constructor
  · intro h
    induction h with
    | pure hab => exact .pure hab
    | liftBind hpos _ ih =>
      obtain rfl := (hS.pos_iff _ _).1 hpos
      exact .liftBind _ fun d => ih d d ((hS.dir_iff _ d d).2 rfl)
  · intro h
    induction h with
    | pure hab => exact .pure hab
    | liftBind a _ ih =>
      refine .liftBind ((hS.pos_iff a a).2 rfl) fun d d' hd => ?_
      obtain rfl := (hS.dir_iff a d d').1 hd
      exact ih d

/-- Leaves are related by the heterogeneous lift exactly when their results are. -/
theorem hFreeRel_pure_iff {R : α → β → Prop} {a : α} {b : β} :
    HFreeRel S R (.pure a : P.FreeM α) (.pure b : Q.FreeM β) ↔ R a b := by
  constructor
  · rintro ⟨h⟩; exact h
  · exact HFreeRel.pure

/-- Two nodes are related by the heterogeneous lift exactly when their positions are related and
their continuations are related at related directions. -/
theorem hFreeRel_liftBind_iff {R : α → β → Prop} {a : P.A} {a' : Q.A}
    {k : P.B a → P.FreeM α} {k' : Q.B a' → Q.FreeM β} :
    HFreeRel S R (.liftBind a k) (.liftBind a' k') ↔
      S.pos a a' ∧ ∀ d d', S.dir a a' d d' → HFreeRel S R (k d) (k' d') := by
  constructor
  · intro h
    cases h
    grind
  · exact fun h => HFreeRel.liftBind h.1 h.2

/-- A leaf and a node are not related by the heterogeneous lift. -/
theorem not_hFreeRel_pure_liftBind {R : α → β → Prop} {a : α} {a' : Q.A}
    {k' : Q.B a' → Q.FreeM β} : ¬ HFreeRel S R (.pure a : P.FreeM α) (.liftBind a' k') := by
  rintro ⟨⟩

/-- A node and a leaf are not related by the heterogeneous lift. -/
theorem not_hFreeRel_liftBind_pure {R : α → β → Prop} {a : P.A} {k : P.B a → P.FreeM α}
    {b : β} : ¬ HFreeRel S R (.liftBind a k) (.pure b : Q.FreeM β) := by
  rintro ⟨⟩

/-- The heterogeneous lift is monotone in the relation on results. -/
theorem HFreeRel.mono {R R' : α → β → Prop} (h : ∀ a b, R a b → R' a b) {x : P.FreeM α}
    {y : Q.FreeM β} (hxy : HFreeRel S R x y) : HFreeRel S R' x y := by
  induction hxy with
  | pure hab => exact .pure (h _ _ hab)
  | liftBind hpos _ ih => exact .liftBind hpos ih

/-- The heterogeneous lift commutes with bind. -/
theorem HFreeRel.bind {γ : Type w} {γ' : Type w'} {R : α → β → Prop} {R' : γ → γ' → Prop}
    {x : P.FreeM α} {y : Q.FreeM β} {f : α → P.FreeM γ} {g : β → Q.FreeM γ'}
    (hxy : HFreeRel S R x y) (hfg : ∀ a b, R a b → HFreeRel S R' (f a) (g b)) :
    HFreeRel S R' (x.bind f) (y.bind g) := by
  induction hxy with
  | pure hab => exact hfg _ _ hab
  | liftBind hpos _ ih => exact .liftBind hpos ih

end HFreeRel

/-! ## Relations between codes of the same shape -/

/-- The signature relation between two sums, componentwise. -/
def SigRel.sum {P₁ Q₁ : PFunctor.{u, v}} {P₂ Q₂ : PFunctor.{u', v'}} (S : SigRel P₁ P₂)
    (T : SigRel Q₁ Q₂) : SigRel (P₁ + Q₁) (P₂ + Q₂) where
  pos
    | .inl a, .inl a' => S.pos a a'
    | .inr b, .inr b' => T.pos b b'
    | _, _ => False
  dir
    | .inl a, .inl a', d, d' => S.dir a a' d d'
    | .inr b, .inr b', d, d' => T.dir b b' d d'
    | _, _, _, _ => False

/-- The componentwise relation of two identity signature relations is an identity. -/
theorem SigRel.IsId.sum {P₁ Q₁ : PFunctor.{u, v}} {S : SigRel P₁ P₁} {T : SigRel Q₁ Q₁}
    (hS : S.IsId) (hT : T.IsId) : (S.sum T).IsId where
  pos_iff a a' := by
    rcases a with a | a <;> rcases a' with a' | a' <;>
      simp [SigRel.sum, hS.pos_iff, hT.pos_iff]
  dir_iff a d d' := by
    rcases a with a | a
    · exact hS.dir_iff a d d'
    · exact hT.dir_iff a d d'

/-- A relation between two operation codes of the same shape: a relation between the types of
corresponding fields, continued at related field values, and a relation between the direction
types. -/
inductive OpRel : OpCode.{u, v} → OpCode.{u', v'} → Type (max (u + 1) (v + 1) (u' + 1) (v' + 1))
  /-- Corresponding fields related by `RS`, continued at related values. -/
  | field {S₁ : Type u} {S₂ : Type u'} {D₁ : S₁ → OpCode.{u, v}} {D₂ : S₂ → OpCode.{u', v'}}
      (RS : S₁ → S₂ → Prop) (RD : ∀ s₁ s₂, RS s₁ s₂ → OpRel (D₁ s₁) (D₂ s₂)) :
      OpRel (.field S₁ D₁) (.field S₂ D₂)
  /-- Direction types related by `RB`. -/
  | dir {B₁ : Type v} {B₂ : Type v'} (RB : B₁ → B₂ → Prop) : OpRel (.dir B₁) (.dir B₂)

namespace OpRel

/-- The relation between the positions of two related operations: the fields are related one
by one. -/
def posRel : {o₁ : OpCode.{u, v}} → {o₂ : OpCode.{u', v'}} → OpRel o₁ o₂ → o₁.Pos → o₂.Pos →
    Prop
  | _, _, .field _ RD, ⟨s₁, p₁⟩, ⟨s₂, p₂⟩ => ∃ h, (RD s₁ s₂ h).posRel p₁ p₂
  | _, _, .dir _, _, _ => True

/-- The relation between the directions of two related operations at two positions. -/
def dirRel : {o₁ : OpCode.{u, v}} → {o₂ : OpCode.{u', v'}} → (r : OpRel o₁ o₂) →
    (p₁ : o₁.Pos) → (p₂ : o₂.Pos) → o₁.Dir p₁ → o₂.Dir p₂ → Prop
  | _, _, .field _ RD, ⟨s₁, p₁⟩, ⟨s₂, p₂⟩, d₁, d₂ => ∀ h, (RD s₁ s₂ h).dirRel p₁ p₂ d₁ d₂
  | _, _, .dir RB, _, _, d₁, d₂ => RB d₁ d₂

/-- The signature relation between the functors of two related operations. -/
def toSigRel {o₁ : OpCode.{u, v}} {o₂ : OpCode.{u', v'}} (r : OpRel o₁ o₂) :
    SigRel o₁.interp o₂.interp :=
  ⟨r.posRel, r.dirRel⟩

/-- The reflexive relation of an operation code: equality on every field and on the
directions. -/
def refl : (o : OpCode.{u, v}) → OpRel o o
  | .field _ D => .field (· = ·) fun s₁ _ h => h ▸ refl (D s₁)
  | .dir _ => .dir (· = ·)

/-- The reflexive relation of an operation code is an identity signature relation. -/
theorem refl_isId (o : OpCode.{u, v}) : (refl o).toSigRel.IsId := by
  induction o with
  | field S D ih =>
    refine ⟨fun ⟨s, p⟩ ⟨s', p'⟩ => ?_, fun ⟨s, p⟩ d d' => ?_⟩
    · constructor
      · rintro ⟨rfl, h⟩
        rw [((ih s).pos_iff p p').1 h]
      · intro h
        cases h
        exact ⟨rfl, ((ih s).pos_iff p p).2 rfl⟩
    · exact ⟨fun h => ((ih s).dir_iff p d d').1 (h rfl),
        fun h _ => ((ih s).dir_iff p d d').2 h⟩
  | dir B => constructor <;> intros <;> simp [refl, toSigRel, posRel, dirRel] <;> rfl

end OpRel

/-- A relation between two codes of the same shape: the operations are related one by one. -/
inductive CodeRel.Ops : List OpCode.{u, v} → List OpCode.{u', v'} →
    Type (max (u + 1) (v + 1) (u' + 1) (v' + 1))
  /-- No operations. -/
  | nil : CodeRel.Ops [] []
  /-- Related first operations and related remaining operations. -/
  | cons {o₁ : OpCode.{u, v}} {o₂ : OpCode.{u', v'}} {os₁ os₂} :
      OpRel o₁ o₂ → CodeRel.Ops os₁ os₂ → CodeRel.Ops (o₁ :: os₁) (o₂ :: os₂)

/-- A relation between two codes of the same shape. -/
abbrev CodeRel (c₁ : Code.{u, v}) (c₂ : Code.{u', v'}) := CodeRel.Ops c₁.ops c₂.ops

namespace CodeRel

/-- The signature relation between the sums of the functors of related lists of operations. -/
def Ops.toSigRel : {os₁ : List OpCode.{u, v}} → {os₂ : List OpCode.{u', v'}} →
    CodeRel.Ops os₁ os₂ → SigRel (OpCode.sum os₁) (OpCode.sum os₂)
  | _, _, .nil => ⟨fun _ _ => False, fun _ _ _ _ => False⟩
  | _, _, .cons r .nil => r.toSigRel
  | _, _, .cons r (.cons r' rs) => SigRel.sum r.toSigRel (Ops.cons r' rs).toSigRel

/-- The signature relation between the functors of two related codes. -/
abbrev toSigRel {c₁ : Code.{u, v}} {c₂ : Code.{u', v'}} (r : CodeRel c₁ c₂) :
    SigRel (Code.interp c₁) (Code.interp c₂) :=
  Ops.toSigRel r

/-- The reflexive relation of a list of operation codes. -/
def Ops.refl : (os : List OpCode.{u, v}) → CodeRel.Ops os os
  | [] => .nil
  | o :: os => .cons (OpRel.refl o) (Ops.refl os)

/-- The reflexive relation of a code: equality on every field and direction. -/
abbrev refl (c : Code.{u, v}) : CodeRel c c := Ops.refl c.ops

/-- The reflexive relation of a list of operation codes is an identity signature relation. -/
theorem Ops.refl_isId : (os : List OpCode.{u, v}) → (Ops.refl os).toSigRel.IsId
  | [] => ⟨fun a => (nomatch a), fun a => (nomatch a)⟩
  | [o] => OpRel.refl_isId o
  | o :: o' :: os => (OpRel.refl_isId o).sum (Ops.refl_isId (o' :: os))

/-- The reflexive relation of a code is an identity signature relation. -/
theorem refl_isId (c : Code.{u, v}) : (refl c).toSigRel.IsId := Ops.refl_isId c.ops

end CodeRel

/-- The heterogeneous lift of `R` to program trees over two codes related by `r`. -/
abbrev Code.HRel {c₁ : Code.{u, v}} {c₂ : Code.{u', v'}} (r : CodeRel c₁ c₂) {α : Type w}
    {β : Type w'} (R : α → β → Prop) :
    (Code.interp c₁).FreeM α → (Code.interp c₂).FreeM β → Prop :=
  HFreeRel r.toSigRel R

/-- The heterogeneous lift along the reflexive relation of a code is `Code.Rel`. -/
theorem Code.hRel_refl_iff (c : Code.{u, v}) {R : α → β → Prop}
    {x : (Code.interp c).FreeM α} {y : (Code.interp c).FreeM β} :
    Code.HRel (CodeRel.refl c) R x y ↔ Code.Rel c R x y :=
  hFreeRel_iff_freeRel (CodeRel.refl_isId c)

/-! ## Relational handlers -/

/-- A relational lifting of the monads `m` and `m'`: a relation `rel R` between computations of
`m α` and `m' β` for each relation `R : α → β → Prop`, with the rule for `pure` (related values
give related computations) and the rule for bind (related computations continued by functions
that send `R`-related results to `R'`-related computations give `R'`-related computations). -/
structure RelLift (m : Type w → Type x) (m' : Type w' → Type x') [Monad m] [Monad m'] where
  /-- The lifted relation between computations. -/
  rel : {α : Type w} → {β : Type w'} → (α → β → Prop) → m α → m' β → Prop
  /-- The rule for `pure`. -/
  rel_pure : ∀ {α : Type w} {β : Type w'} {R : α → β → Prop} {a : α} {b : β}, R a b →
    rel R (pure a) (pure b)
  /-- The rule for bind. -/
  rel_bind : ∀ {α γ : Type w} {β δ : Type w'} {R : α → β → Prop} {R' : γ → δ → Prop}
    {c : m α} {c' : m' β} {f : α → m γ} {g : β → m' δ}, rel R c c' →
    (∀ a b, R a b → rel R' (f a) (g b)) → rel R' (c >>= f) (c' >>= g)

/-- **Relational handlers.** Handlers `h` of `P` in `m` and `h'` of `Q` in `m'` that send
positions related by `S` to computations related by the lifting of the direction relation
interpret programs related by `HFreeRel S R` to computations related by the lifting of `R`. -/
theorem HFreeRel.liftM_rel {Q : PFunctor.{u', v'}} {S : SigRel P Q} {m : Type v → Type x}
    {m' : Type v' → Type x'} [Monad m] [Monad m'] (L : RelLift m m')
    {h : (a : P.A) → m (P.B a)} {h' : (a' : Q.A) → m' (Q.B a')}
    (hh : ∀ a a', S.pos a a' → L.rel (S.dir a a') (h a) (h' a'))
    {α : Type v} {β : Type v'} {R : α → β → Prop} {x : P.FreeM α} {y : Q.FreeM β}
    (hxy : HFreeRel S R x y) : L.rel R (x.liftM h) (y.liftM h') := by
  induction hxy with
  | pure hab => exact L.rel_pure hab
  | liftBind hpos _ ih => exact L.rel_bind (hh _ _ hpos) ih

end CatCrypt.Container

end
