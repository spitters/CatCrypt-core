/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.Basic


@[expose] public section
set_option autoImplicit false

/-!
# `XCorePT`: graded predicate transformers over an assertion type

A graded predicate transformer `XCorePT Pred EPred G α` is a monotone map
`(α → Pred) → EPred → Pred` together with a grade `g : G`. The parameters are an
assertion type `Pred`, an exception-postcondition type `EPred`, a grade type `G`
and a result type `α`. No index describes the effect stack: a state layer is a
function type inside `Pred`, an exception layer a component of `EPred`. This is
the parameterisation of the predicate transformers of Lean's standard library
(`Pred`, `EPred`), with the grade as an additional parameter.

The structure needs `≤` on `Pred` and `EPred` only. The laws state the order
class they use: the sequencing, frame and relational rules use transitivity on
`Pred` and reflexivity on `EPred` (`Preorder` on both); the transfer rule and
the grade equations use `≤` alone; the budget rule uses a preorder on `G` with
monotone addition.

## Main definitions

* `XCorePT`: the transformer, with fields `apply`, `grade`, `mono`.
* `XCorePT.ret`, `XCorePT.bind`, `XCorePT.seq`, `XCorePT.prod`: return (grade
  `0`), bind (grade of the head), sequencing (grades add), product.
* `XCorePT.Triple`: the Hoare triple `P ≤ t.apply post epost`.
* `XCoreSep`, `XCorePT.Local`: a separating product monotone in its left
  argument, and the frame property of a transformer.
* `XCorePT.mapGrade`, `XCoreHom`, `XCoreHom.map`: change of grade, and change of
  assertions and grade together.
* `XCoreWP`, `XCoreWP.Triple`, `LawfulXCoreWP`: the observation of a monad as
  transformers, the triple of a program, and commutation of the observation with
  `pure` and `bind`.
* `XCoreWPHom`, `XCoreHom.toWPHom`: a morphism of observations with a joint map
  on the pair of postconditions, and the componentwise case.

## Main results

* `XCorePT.bind_mono`, `XCorePT.seq_mono`: bind and sequencing are monotone in
  the refinement order.
* `XCorePT.seq_grade`, `XCorePT.seq_grade_le`: the grade of a sequence is the
  sum, and stays within the sum of two budgets.
* `XCorePT.seq_triple`, `XCorePT.bind_triple`: Hoare composition.
* `XCorePT.frame`, `XCorePT.ret_local`, `XCorePT.bind_local`,
  `XCorePT.seq_local`: the frame rule and closure of locality.
* `XCorePT.rel_seq`: relational sequencing over the product.
* `XCorePT.Triple.transfer`, `XCoreHom.map_triple`, `XCoreHom.map_ret`,
  `XCoreHom.map_bind`, `XCoreHom.map_seq`: transfer of triples along a change of
  assertions, and its commutation with return, bind and sequencing.
* `XCoreWP.pure_triple`, `XCoreWP.bind_triple`, `XCoreWP.bind_grade`: the rules
  of a lawful observation.
* `XCoreWP.seq_triple_of_wp_eq`: graded sequencing for programs whose
  observation is a sequence, as in a family of monads indexed by the grade.
* `XCoreWPHom.triple`: transfer of triples along a morphism of observations.
-/

namespace CatCrypt.XDijkstra

universe u v w x y z

/-- A graded predicate transformer: a monotone weakest-precondition map from a
postcondition `α → Pred` and an exception postcondition `EPred` to a
precondition `Pred`, with a grade value in `G`. -/
structure XCorePT (Pred : Type u) (EPred : Type v) (G : Type w) [LE Pred] [LE EPred]
    (α : Type x) : Type (max u v w x) where
  /-- The weakest-precondition map. -/
  apply : (α → Pred) → EPred → Pred
  /-- The grade value. -/
  grade : G
  /-- Weaker postconditions give a weaker precondition. -/
  mono : ∀ {post post' : α → Pred} {epost epost' : EPred},
    (∀ a, post a ≤ post' a) → epost ≤ epost' → apply post epost ≤ apply post' epost'

namespace XCorePT

variable {Pred : Type u} {EPred : Type v} {G : Type w}

/-! ## Return, bind, sequencing, product -/

section Ops

variable [LE Pred] [LE EPred] {α : Type x} {β : Type y}

/-- Two transformers are equal when their weakest-precondition maps and their
grades agree. -/
theorem ext {s t : XCorePT Pred EPred G α}
    (happly : ∀ (post : α → Pred) (epost : EPred), s.apply post epost = t.apply post epost)
    (hgrade : s.grade = t.grade) : s = t := by
  obtain ⟨sa, sg, _⟩ := s
  obtain ⟨ta, tg, _⟩ := t
  obtain rfl : sa = ta := funext fun post => funext fun epost => happly post epost
  obtain rfl : sg = tg := hgrade
  rfl

/-- Return: the postcondition at the returned value, at grade `0`. -/
def ret [Zero G] (a : α) : XCorePT Pred EPred G α where
  apply post _ := post a
  grade := 0
  mono h _ := h a

/-- Bind: composition of the weakest-precondition maps. The grade is that of the
head, since a value-dependent continuation has no single grade to add. -/
def bind (t : XCorePT Pred EPred G α) (f : α → XCorePT Pred EPred G β) :
    XCorePT Pred EPred G β where
  apply post epost := t.apply (fun a => (f a).apply post epost) epost
  grade := t.grade
  mono h he := t.mono (fun a => (f a).mono h he) he

/-- Sequencing with a constant continuation: the grades add. -/
def seq [Add G] (s : XCorePT Pred EPred G α) (t : XCorePT Pred EPred G β) :
    XCorePT Pred EPred G β where
  apply post epost := s.apply (fun _ => t.apply post epost) epost
  grade := s.grade + t.grade
  mono h he := s.mono (fun _ => t.mono h he) he

/-- Product: run `s`, then `t`, and pair the results. The grade is that of `s`. -/
def prod (s : XCorePT Pred EPred G α) (t : XCorePT Pred EPred G β) :
    XCorePT Pred EPred G (α × β) where
  apply post epost := s.apply (fun a => t.apply (fun b => post (a, b)) epost) epost
  grade := s.grade
  mono h he := s.mono (fun a => t.mono (fun b => h (a, b)) he) he

/-- Change of grade along a function. -/
def mapGrade {H : Type w} (φ : G → H) (t : XCorePT Pred EPred G α) :
    XCorePT Pred EPred H α where
  apply := t.apply
  grade := φ t.grade
  mono := t.mono

@[simp] theorem ret_apply [Zero G] (a : α) (post : α → Pred) (epost : EPred) :
    (ret (G := G) a).apply post epost = post a := rfl

@[simp] theorem ret_grade [Zero G] (a : α) :
    (ret (Pred := Pred) (EPred := EPred) (G := G) a).grade = 0 := rfl

@[simp] theorem bind_apply (t : XCorePT Pred EPred G α) (f : α → XCorePT Pred EPred G β)
    (post : β → Pred) (epost : EPred) :
    (t.bind f).apply post epost = t.apply (fun a => (f a).apply post epost) epost := rfl

@[simp] theorem bind_grade (t : XCorePT Pred EPred G α) (f : α → XCorePT Pred EPred G β) :
    (t.bind f).grade = t.grade := rfl

@[simp] theorem seq_apply [Add G] (s : XCorePT Pred EPred G α) (t : XCorePT Pred EPred G β)
    (post : β → Pred) (epost : EPred) :
    (s.seq t).apply post epost = s.apply (fun _ => t.apply post epost) epost := rfl

/-- The grade of a sequence is the sum of the grades. -/
@[simp] theorem seq_grade [Add G] (s : XCorePT Pred EPred G α) (t : XCorePT Pred EPred G β) :
    (s.seq t).grade = s.grade + t.grade := rfl

@[simp] theorem prod_apply (s : XCorePT Pred EPred G α) (t : XCorePT Pred EPred G β)
    (post : α × β → Pred) (epost : EPred) :
    (s.prod t).apply post epost
      = s.apply (fun a => t.apply (fun b => post (a, b)) epost) epost := rfl

@[simp] theorem mapGrade_apply {H : Type w} (φ : G → H) (t : XCorePT Pred EPred G α) :
    (t.mapGrade φ).apply = t.apply := rfl

@[simp] theorem mapGrade_grade {H : Type w} (φ : G → H) (t : XCorePT Pred EPred G α) :
    (t.mapGrade φ).grade = φ t.grade := rfl

/-- Left identity of bind on the weakest-precondition map. -/
theorem ret_bind_apply [Zero G] (a : α) (f : α → XCorePT Pred EPred G β)
    (post : β → Pred) (epost : EPred) :
    ((ret a).bind f).apply post epost = (f a).apply post epost := rfl

/-- Right identity of bind. -/
theorem bind_ret [Zero G] (t : XCorePT Pred EPred G α) :
    t.bind (fun a => ret a) = t := ext (fun _ _ => rfl) rfl

/-- Associativity of bind. -/
theorem bind_assoc {γ : Type x} (t : XCorePT Pred EPred G α) (f : α → XCorePT Pred EPred G β)
    (g : β → XCorePT Pred EPred G γ) :
    (t.bind f).bind g = t.bind (fun a => (f a).bind g) := ext (fun _ _ => rfl) rfl

/-- A change of grade that preserves addition commutes with sequencing. -/
theorem mapGrade_seq {H : Type w} [Add G] [Add H] (φ : G → H)
    (hφ : ∀ a b : G, φ (a + b) = φ a + φ b)
    (s : XCorePT Pred EPred G α) (t : XCorePT Pred EPred G β) :
    (s.seq t).mapGrade φ = (s.mapGrade φ).seq (t.mapGrade φ) :=
  ext (fun _ _ => rfl) (hφ s.grade t.grade)

/-- A change of grade that preserves `0` commutes with return. -/
theorem mapGrade_ret {H : Type w} [Zero G] [Zero H] (φ : G → H) (hφ : φ 0 = 0) (a : α) :
    (ret (Pred := Pred) (EPred := EPred) a).mapGrade φ = ret a :=
  ext (fun _ _ => rfl) hφ

/-- The budget rule: two sequenced steps within budgets `b₁` and `b₂` stay within
`b₁ + b₂`. -/
theorem seq_grade_le [Add G] [Preorder G] [AddLeftMono G] [AddRightMono G]
    (s : XCorePT Pred EPred G α) (t : XCorePT Pred EPred G β) {b₁ b₂ : G}
    (h₁ : s.grade ≤ b₁) (h₂ : t.grade ≤ b₂) : (s.seq t).grade ≤ b₁ + b₂ :=
  add_le_add h₁ h₂

/-- The Hoare triple of a transformer: the precondition `P` entails the weakest
precondition at `post` and `epost`. -/
def Triple (P : Pred) (t : XCorePT Pred EPred G α) (post : α → Pred) (epost : EPred) : Prop :=
  P ≤ t.apply post epost

/-- Transfer of a triple along a monotone precondition map: if the weakest
precondition of `t'` is the image under `pre` of that of `t`, a triple for `t`
gives a triple for `t'`. -/
theorem Triple.transfer {Pred' : Type u} {EPred' : Type v} {G' : Type w}
    [LE Pred'] [LE EPred'] {pre : Pred → Pred'}
    (hpre : ∀ {A B : Pred}, A ≤ B → pre A ≤ pre B)
    {t : XCorePT Pred EPred G α} {t' : XCorePT Pred' EPred' G' α}
    {post : α → Pred} {epost : EPred} {post' : α → Pred'} {epost' : EPred'}
    (htr : t'.apply post' epost' = pre (t.apply post epost))
    {P : Pred} (h : Triple P t post epost) : Triple (pre P) t' post' epost' := by
  unfold Triple
  rw [htr]
  exact hpre h

end Ops

/-! ## The refinement order and the composition rules -/

section Order

variable {α : Type x} {β : Type y}

/-- Refinement: pointwise order of the weakest-precondition maps. The grade is
not compared. -/
instance instLE [LE Pred] [LE EPred] : LE (XCorePT Pred EPred G α) :=
  ⟨fun s t => ∀ (post : α → Pred) (epost : EPred), s.apply post epost ≤ t.apply post epost⟩

theorem le_def [LE Pred] [LE EPred] {s t : XCorePT Pred EPred G α} :
    s ≤ t ↔ ∀ (post : α → Pred) (epost : EPred), s.apply post epost ≤ t.apply post epost :=
  Iff.rfl

instance instPreorder [Preorder Pred] [LE EPred] : Preorder (XCorePT Pred EPred G α) where
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ post epost := le_trans (h₁ post epost) (h₂ post epost)

variable [Preorder Pred]

/-- Bind is monotone in the head and in the continuation. -/
theorem bind_mono [Preorder EPred] {s s' : XCorePT Pred EPred G α}
    {f f' : α → XCorePT Pred EPred G β} (hs : s ≤ s') (hf : ∀ a, f a ≤ f' a) :
    s.bind f ≤ s'.bind f' := fun post epost =>
  le_trans (s.mono (fun a => hf a post epost) le_rfl) (hs _ epost)

/-- Sequencing is monotone in both arguments. -/
theorem seq_mono [Preorder EPred] [Add G] {s s' : XCorePT Pred EPred G α}
    {t t' : XCorePT Pred EPred G β} (hs : s ≤ s') (ht : t ≤ t') :
    s.seq t ≤ s'.seq t' := fun post epost =>
  le_trans (s.mono (fun _ => ht post epost) le_rfl) (hs _ epost)

/-- Consequence: strengthen the precondition, weaken both postconditions. -/
theorem Triple.conseq [LE EPred] {t : XCorePT Pred EPred G α} {P P' : Pred}
    {post post' : α → Pred} {epost epost' : EPred} (h : Triple P t post epost)
    (hP : P' ≤ P) (hpost : ∀ a, post a ≤ post' a) (hepost : epost ≤ epost') :
    Triple P' t post' epost' :=
  le_trans hP (le_trans h (t.mono hpost hepost))

/-- Hoare composition for bind, with an intermediate assertion per value. -/
theorem bind_triple [Preorder EPred] {s : XCorePT Pred EPred G α}
    {f : α → XCorePT Pred EPred G β} {P : Pred} {R : α → Pred} {post : β → Pred}
    {epost : EPred} (h₁ : Triple P s R epost) (h₂ : ∀ a, Triple (R a) (f a) post epost) :
    Triple P (s.bind f) post epost :=
  le_trans h₁ (s.mono h₂ le_rfl)

/-- Hoare composition for sequencing; the grade of the composite is the sum
(`seq_grade`). -/
theorem seq_triple [Preorder EPred] [Add G] {s : XCorePT Pred EPred G α}
    {t : XCorePT Pred EPred G β} {P R : Pred} {post : β → Pred} {epost : EPred}
    (h₁ : Triple P s (fun _ => R) epost) (h₂ : Triple R t post epost) :
    Triple P (s.seq t) post epost :=
  le_trans h₁ (s.mono (fun _ => h₂) le_rfl)

/-- The relational judgment: a triple over the product transformer. -/
def RelTriple [LE EPred] (P : Pred) (s : XCorePT Pred EPred G α) (t : XCorePT Pred EPred G β)
    (Ψ : α × β → Pred) (epost : EPred) : Prop :=
  Triple P (s.prod t) Ψ epost

/-- Relational sequencing: `s` takes `P` to `R a`, and for each `a` the
transformer `t` takes `R a` to `Ψ (a, b)`. -/
theorem rel_seq [Preorder EPred] {s : XCorePT Pred EPred G α} {t : XCorePT Pred EPred G β}
    {P : Pred} {R : α → Pred} {Ψ : α × β → Pred} {epost : EPred}
    (h₁ : Triple P s R epost) (h₂ : ∀ a, Triple (R a) t (fun b => Ψ (a, b)) epost) :
    RelTriple P s t Ψ epost :=
  le_trans h₁ (s.mono h₂ le_rfl)

end Order

end XCorePT

/-! ## Separation: the frame rule -/

/-- A separating product on an assertion type, monotone in its left argument.
The frame rule uses no other property of the product. -/
class XCoreSep (Pred : Type u) [LE Pred] where
  /-- The separating product. -/
  sep : Pred → Pred → Pred
  /-- The product is monotone in its left argument. -/
  sep_mono_left : ∀ {a b : Pred} (r : Pred), a ≤ b → sep a r ≤ sep b r

namespace XCorePT

section Frame

variable {Pred : Type u} {EPred : Type v} {G : Type w} {α : Type x} {β : Type y}

/-- Locality: the weakest precondition absorbs a framed assertion. -/
def Local [LE Pred] [LE EPred] [XCoreSep Pred] (t : XCorePT Pred EPred G α) : Prop :=
  ∀ (post : α → Pred) (epost : EPred) (R : Pred),
    XCoreSep.sep (t.apply post epost) R ≤ t.apply (fun a => XCoreSep.sep (post a) R) epost

variable [Preorder Pred]

/-- The frame rule: a triple of a local transformer extends by a frame `R` on
the precondition and on the postcondition. -/
theorem frame [LE EPred] [XCoreSep Pred] {t : XCorePT Pred EPred G α} (hloc : t.Local)
    {P R : Pred} {post : α → Pred} {epost : EPred} (h : Triple P t post epost) :
    Triple (XCoreSep.sep P R) t (fun a => XCoreSep.sep (post a) R) epost :=
  le_trans (XCoreSep.sep_mono_left R h) (hloc post epost R)

/-- Return is local. -/
theorem ret_local [LE EPred] [XCoreSep Pred] [Zero G] (a : α) :
    (ret (Pred := Pred) (EPred := EPred) (G := G) a).Local :=
  fun _ _ _ => le_rfl

/-- Locality is closed under bind. -/
theorem bind_local [Preorder EPred] [XCoreSep Pred] {s : XCorePT Pred EPred G α}
    {f : α → XCorePT Pred EPred G β} (hs : s.Local) (hf : ∀ a, (f a).Local) :
    (s.bind f).Local := fun post epost R =>
  le_trans (hs _ epost R) (s.mono (fun a => hf a post epost R) le_rfl)

/-- Locality is closed under sequencing. -/
theorem seq_local [Preorder EPred] [XCoreSep Pred] [Add G] {s : XCorePT Pred EPred G α}
    {t : XCorePT Pred EPred G β} (hs : s.Local) (ht : t.Local) :
    (s.seq t).Local := fun post epost R =>
  le_trans (hs _ epost R) (s.mono (fun _ => ht post epost R) le_rfl)

end Frame

end XCorePT

/-! ## Change of assertions and grade -/

/-- A change of assertions and grade: a precondition map `pre`, postcondition
maps `post` and `epost` in the opposite direction, all monotone, and a grade
map. -/
structure XCoreHom (Pred₁ : Type u) (EPred₁ : Type v) (G₁ : Type w)
    (Pred₂ : Type u) (EPred₂ : Type v) (G₂ : Type w)
    [LE Pred₁] [LE EPred₁] [LE Pred₂] [LE EPred₂] where
  /-- The map on preconditions. -/
  pre : Pred₁ → Pred₂
  /-- The map on postconditions. -/
  post : Pred₂ → Pred₁
  /-- The map on exception postconditions. -/
  epost : EPred₂ → EPred₁
  /-- The map on grades. -/
  grade : G₁ → G₂
  /-- `pre` is monotone. -/
  pre_mono : ∀ {A B : Pred₁}, A ≤ B → pre A ≤ pre B
  /-- `post` is monotone. -/
  post_mono : ∀ {A B : Pred₂}, A ≤ B → post A ≤ post B
  /-- `epost` is monotone. -/
  epost_mono : ∀ {A B : EPred₂}, A ≤ B → epost A ≤ epost B

namespace XCoreHom

variable {Pred₁ : Type u} {EPred₁ : Type v} {G₁ : Type w}
  {Pred₂ : Type u} {EPred₂ : Type v} {G₂ : Type w}
  [LE Pred₁] [LE EPred₁] [LE Pred₂] [LE EPred₂] {α : Type x} {β : Type y}

/-- The action on transformers: pull the postconditions back, apply the
transformer, push the precondition forward. -/
def map (θ : XCoreHom Pred₁ EPred₁ G₁ Pred₂ EPred₂ G₂) (t : XCorePT Pred₁ EPred₁ G₁ α) :
    XCorePT Pred₂ EPred₂ G₂ α where
  apply post epost := θ.pre (t.apply (fun a => θ.post (post a)) (θ.epost epost))
  grade := θ.grade t.grade
  mono h he := θ.pre_mono (t.mono (fun a => θ.post_mono (h a)) (θ.epost_mono he))

@[simp] theorem map_apply (θ : XCoreHom Pred₁ EPred₁ G₁ Pred₂ EPred₂ G₂)
    (t : XCorePT Pred₁ EPred₁ G₁ α) (post : α → Pred₂) (epost : EPred₂) :
    (θ.map t).apply post epost
      = θ.pre (t.apply (fun a => θ.post (post a)) (θ.epost epost)) := rfl

@[simp] theorem map_grade (θ : XCoreHom Pred₁ EPred₁ G₁ Pred₂ EPred₂ G₂)
    (t : XCorePT Pred₁ EPred₁ G₁ α) : (θ.map t).grade = θ.grade t.grade := rfl

/-- Transfer of triples: a triple for `t` at the pulled-back postconditions gives
a triple for `θ.map t` at the pushed-forward precondition. -/
theorem map_triple (θ : XCoreHom Pred₁ EPred₁ G₁ Pred₂ EPred₂ G₂)
    {t : XCorePT Pred₁ EPred₁ G₁ α} {P : Pred₁} {post : α → Pred₂} {epost : EPred₂}
    (h : XCorePT.Triple P t (fun a => θ.post (post a)) (θ.epost epost)) :
    XCorePT.Triple (θ.pre P) (θ.map t) post epost :=
  XCorePT.Triple.transfer θ.pre_mono rfl h

/-- The action commutes with return when `pre` is a left inverse of `post` and
the grade map preserves `0`. -/
theorem map_ret [Zero G₁] [Zero G₂] (θ : XCoreHom Pred₁ EPred₁ G₁ Pred₂ EPred₂ G₂)
    (hsec : ∀ B : Pred₂, θ.pre (θ.post B) = B) (hzero : θ.grade 0 = 0) (a : α) :
    θ.map (XCorePT.ret a) = XCorePT.ret a :=
  XCorePT.ext (fun post _ => hsec (post a)) hzero

/-- The action commutes with bind when `post` is a left inverse of `pre`. -/
theorem map_bind (θ : XCoreHom Pred₁ EPred₁ G₁ Pred₂ EPred₂ G₂)
    (hret : ∀ A : Pred₁, θ.post (θ.pre A) = A)
    (t : XCorePT Pred₁ EPred₁ G₁ α) (f : α → XCorePT Pred₁ EPred₁ G₁ β) :
    θ.map (t.bind f) = (θ.map t).bind (fun a => θ.map (f a)) :=
  XCorePT.ext (fun post epost => by simp [hret]) rfl

/-- The action commutes with sequencing when `post` is a left inverse of `pre`
and the grade map preserves addition. -/
theorem map_seq [Add G₁] [Add G₂] (θ : XCoreHom Pred₁ EPred₁ G₁ Pred₂ EPred₂ G₂)
    (hret : ∀ A : Pred₁, θ.post (θ.pre A) = A)
    (hadd : ∀ a b : G₁, θ.grade (a + b) = θ.grade a + θ.grade b)
    (s : XCorePT Pred₁ EPred₁ G₁ α) (t : XCorePT Pred₁ EPred₁ G₁ β) :
    θ.map (s.seq t) = (θ.map s).seq (θ.map t) :=
  XCorePT.ext (fun post epost => by simp [hret]) (hadd s.grade t.grade)

end XCoreHom

/-! ## Observation of a monad

`XCoreWP m Pred EPred G` observes the programs of `m` as transformers over the
assertion types `Pred` and `EPred`. The assertion types are ordinary parameters:
one monad may be observed at several assertion types, and a triple names them in
its precondition and postconditions. The grade type is an output parameter: it
occurs in no argument of a triple, so it is determined from the monad and the
assertion types. -/

/-- A weakest-precondition observation of the programs of `m` as graded
transformers over the assertion type `Pred`, the exception-postcondition type
`EPred` and the grade type `G`. -/
class XCoreWP (m : Type x → Type y) (Pred : Type u) (EPred : Type v)
    (G : outParam (Type w)) [LE Pred] [LE EPred] where
  /-- The transformer of a program. -/
  wp {α : Type x} : m α → XCorePT Pred EPred G α

namespace XCoreWP

variable {m : Type x → Type y} {Pred : Type u} {EPred : Type v} {G : Type w}

/-- The Hoare triple of a program: the triple of its transformer. -/
def Triple [LE Pred] [LE EPred] [XCoreWP m Pred EPred G] {α : Type x}
    (P : Pred) (c : m α) (post : α → Pred) (epost : EPred) : Prop :=
  XCorePT.Triple P (wp c) post epost

/-- Consequence for the triple of a program. -/
theorem Triple.conseq [Preorder Pred] [LE EPred] [XCoreWP m Pred EPred G] {α : Type x}
    {c : m α} {P P' : Pred} {post post' : α → Pred} {epost epost' : EPred}
    (h : Triple P c post epost) (hP : P' ≤ P) (hpost : ∀ a, post a ≤ post' a)
    (hepost : epost ≤ epost') : Triple P' c post' epost' :=
  XCorePT.Triple.conseq h hP hpost hepost

/-- Graded sequencing for three observed programs, which may belong to three
members of a family of monads indexed by the grade. If the transformer of `e` is
the sequence of the transformers of `c` and `d`, then triples of `c` and `d`
compose to a triple of `e`, and the grade of `e` is the sum of the grades. -/
theorem seq_triple_of_wp_eq {m₁ m₂ m₃ : Type x → Type y}
    [Preorder Pred] [Preorder EPred] [Add G]
    [XCoreWP m₁ Pred EPred G] [XCoreWP m₂ Pred EPred G] [XCoreWP m₃ Pred EPred G]
    {α β : Type x} {c : m₁ α} {d : m₂ β} {e : m₃ β}
    (he : (wp e : XCorePT Pred EPred G β) = (wp c : XCorePT Pred EPred G α).seq (wp d))
    {P R : Pred} {post : β → Pred} {epost : EPred}
    (h₁ : Triple P c (fun _ => R) epost) (h₂ : Triple R d post epost) :
    Triple P e post epost
      ∧ (wp e : XCorePT Pred EPred G β).grade
          = (wp c : XCorePT Pred EPred G α).grade + (wp d : XCorePT Pred EPred G β).grade := by
  unfold Triple at *
  rw [he]
  exact ⟨XCorePT.seq_triple h₁ h₂, rfl⟩

end XCoreWP

/-- A transformer observes itself. -/
instance XCorePT.instXCoreWP {Pred : Type u} {EPred : Type v} {G : Type w}
    [LE Pred] [LE EPred] : XCoreWP (XCorePT.{u, v, w, x} Pred EPred G) Pred EPred G where
  wp := id

/-- The observation of a transformer is the transformer. -/
@[simp] theorem XCorePT.wp_self {Pred : Type u} {EPred : Type v} {G : Type w}
    [LE Pred] [LE EPred] {α : Type x} (t : XCorePT Pred EPred G α) :
    (XCoreWP.wp t : XCorePT Pred EPred G α) = t := rfl

/-- The observation of a monad commutes with `pure` and `bind`: `pure` is
observed as `XCorePT.ret`, at grade `0`, and `bind` as `XCorePT.bind`, at the
grade of the head. -/
class LawfulXCoreWP (m : Type x → Type y) (Pred : Type u) (EPred : Type v)
    {G : Type w} [Monad m] [LE Pred] [LE EPred] [Zero G] [XCoreWP m Pred EPred G] :
    Prop where
  /-- `pure` is observed as return. -/
  wp_pure {α : Type x} (a : α) :
    (XCoreWP.wp (pure a : m α) : XCorePT Pred EPred G α) = XCorePT.ret a
  /-- `bind` is observed as the bind of the observations. -/
  wp_bind {α β : Type x} (c : m α) (f : α → m β) :
    (XCoreWP.wp (c >>= f) : XCorePT Pred EPred G β)
      = (XCoreWP.wp c : XCorePT Pred EPred G α).bind (fun a => XCoreWP.wp (f a))

namespace XCoreWP

variable {m : Type x → Type y} {Pred : Type u} {EPred : Type v} {G : Type w}

/-- The triple of `pure a` from the postcondition at `a`. -/
theorem pure_triple [Monad m] [Preorder Pred] [LE EPred] [Zero G] [XCoreWP m Pred EPred G]
    [LawfulXCoreWP m Pred EPred] {α : Type x} (a : α) (post : α → Pred) (epost : EPred) :
    Triple (post a) (pure a : m α) post epost := by
  unfold Triple
  rw [LawfulXCoreWP.wp_pure]
  exact le_refl (post a)

/-- Hoare composition for `bind` in a monad with a lawful observation. -/
theorem bind_triple [Monad m] [Preorder Pred] [Preorder EPred] [Zero G]
    [XCoreWP m Pred EPred G] [LawfulXCoreWP m Pred EPred] {α β : Type x} {c : m α}
    {f : α → m β} {P : Pred} {R : α → Pred} {post : β → Pred} {epost : EPred}
    (h₁ : Triple P c R epost) (h₂ : ∀ a, Triple (R a) (f a) post epost) :
    Triple P (c >>= f) post epost := by
  unfold Triple at *
  rw [LawfulXCoreWP.wp_bind]
  exact XCorePT.bind_triple h₁ h₂

/-- The grade of a `bind` is the grade of its head. -/
theorem bind_grade [Monad m] [LE Pred] [LE EPred] [Zero G] [XCoreWP m Pred EPred G]
    [LawfulXCoreWP m Pred EPred] {α β : Type x} (c : m α) (f : α → m β) :
    (wp (c >>= f) : XCorePT Pred EPred G β).grade
      = (wp c : XCorePT Pred EPred G α).grade := by
  rw [LawfulXCoreWP.wp_bind]; rfl

end XCoreWP

/-! ## Morphisms of observations -/

/-- A morphism of observations along `θ : m → n`: a map `postMap` on the pair of
a postcondition and an exception postcondition, a monotone map `preMap` on
preconditions, and the transfer law relating the two observations. The map
`postMap` acts on the pair jointly, so the pulled-back postcondition may depend
on the exception postcondition and conversely. -/
structure XCoreWPHom {m : Type x → Type y} {n : Type x → Type z}
    (Pred₁ : Type u) (EPred₁ : Type v) (Pred₂ : Type u) (EPred₂ : Type v)
    {G₁ G₂ : Type w} [LE Pred₁] [LE EPred₁] [LE Pred₂] [LE EPred₂]
    [XCoreWP m Pred₁ EPred₁ G₁] [XCoreWP n Pred₂ EPred₂ G₂]
    (θ : {α : Type x} → m α → n α) where
  /-- The map from postcondition pairs of `n` to postcondition pairs of `m`. -/
  postMap : {α : Type x} → (α → Pred₂) × EPred₂ → (α → Pred₁) × EPred₁
  /-- The map on preconditions. -/
  preMap : Pred₁ → Pred₂
  /-- `preMap` is monotone. -/
  preMap_mono : ∀ {A B : Pred₁}, A ≤ B → preMap A ≤ preMap B
  /-- The weakest precondition of `θ c` is the image under `preMap` of that of
  `c` at the pulled-back pair. -/
  transfer : ∀ {α : Type x} (c : m α) (post : α → Pred₂) (epost : EPred₂),
    (XCoreWP.wp (θ c : n α) : XCorePT Pred₂ EPred₂ G₂ α).apply post epost
      = preMap ((XCoreWP.wp c : XCorePT Pred₁ EPred₁ G₁ α).apply
          (postMap (post, epost)).1 (postMap (post, epost)).2)

namespace XCoreWPHom

variable {m : Type x → Type y} {n : Type x → Type z}
  {Pred₁ : Type u} {EPred₁ : Type v} {Pred₂ : Type u} {EPred₂ : Type v} {G₁ G₂ : Type w}
  [LE Pred₁] [LE EPred₁] [LE Pred₂] [LE EPred₂]
  [XCoreWP m Pred₁ EPred₁ G₁] [XCoreWP n Pred₂ EPred₂ G₂] {θ : {α : Type x} → m α → n α}

/-- Transfer of triples along a morphism of observations: a triple of `c` at the
pulled-back pair gives a triple of `θ c` at the image of the precondition. -/
theorem triple (φ : XCoreWPHom (m := m) (n := n) Pred₁ EPred₁ Pred₂ EPred₂ θ)
    {α : Type x} (c : m α)
    {P : Pred₁} {post : α → Pred₂} {epost : EPred₂}
    (h : XCoreWP.Triple P c (φ.postMap (post, epost)).1 (φ.postMap (post, epost)).2) :
    XCoreWP.Triple (m := n) (φ.preMap P) (θ c : n α) post epost :=
  XCorePT.Triple.transfer φ.preMap_mono (φ.transfer c post epost) h

end XCoreWPHom

/-- A change of assertions is a morphism of the self-observations along its
action on transformers; `postMap` acts on each component separately. -/
def XCoreHom.toWPHom {Pred₁ : Type u} {EPred₁ : Type v} {G₁ : Type w}
    {Pred₂ : Type u} {EPred₂ : Type v} {G₂ : Type w}
    [LE Pred₁] [LE EPred₁] [LE Pred₂] [LE EPred₂]
    (θ : XCoreHom Pred₁ EPred₁ G₁ Pred₂ EPred₂ G₂) :
    XCoreWPHom (m := XCorePT.{u, v, w, x} Pred₁ EPred₁ G₁)
      (n := XCorePT.{u, v, w, x} Pred₂ EPred₂ G₂)
      Pred₁ EPred₁ Pred₂ EPred₂ (fun {_} t => θ.map t) where
  postMap Q := (fun a => θ.post (Q.1 a), θ.epost Q.2)
  preMap := θ.pre
  preMap_mono := θ.pre_mono
  transfer _ _ _ := rfl

/-- The transfer rule of a change of assertions, obtained from the transfer rule
of its morphism of observations; the statement is that of `XCoreHom.map_triple`. -/
theorem XCoreHom.toWPHom_triple {Pred₁ : Type u} {EPred₁ : Type v} {G₁ : Type w}
    {Pred₂ : Type u} {EPred₂ : Type v} {G₂ : Type w}
    [LE Pred₁] [LE EPred₁] [LE Pred₂] [LE EPred₂]
    (θ : XCoreHom Pred₁ EPred₁ G₁ Pred₂ EPred₂ G₂) {α : Type x}
    {t : XCorePT Pred₁ EPred₁ G₁ α} {P : Pred₁} {post : α → Pred₂} {epost : EPred₂}
    (h : XCorePT.Triple P t (fun a => θ.post (post a)) (θ.epost epost)) :
    XCorePT.Triple (θ.pre P) (θ.map t) post epost :=
  θ.toWPHom.triple t h

end CatCrypt.XDijkstra
