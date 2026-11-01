/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Category.TracedTerm
public import CatCryptCore.Crypto.Party.Compose
public import CatCryptCore.Crypto.Party.QProg
public import CatCryptCore.Crypto.UCLoopbackTraced
public import CatCryptCore.Quantum.QSysCat

/-!
# The traced symmetric monoidal category of party programs

A wiring diagram of party programs is a term `WTerm Gen X Y` (the term syntax of
`CatCryptCore.Category.TracedTerm`) built from generators `Gen X Y` by identities, sequence,
tensor, the structure maps of a symmetric monoidal category (associators, unitors, symmetry)
and the trace. Given a traced symmetric monoidal category `C`
and a denotation `g` of the generators, a term denotes the morphism `WTerm.den g t` of `C`. The
category `Diag g` has the objects of `C` and, as morphisms, terms modulo equality of their
denotations; its composition, tensor and trace are the term constructors. It is a traced
symmetric monoidal category, and the denotation is a strict traced symmetric monoidal functor
`Diag.functor g : Diag g ⥤ C` that is faithful: the meaning of every composite of generators is
the composite of their meanings, by functoriality.

The party language gives two instances. In the classical one (`PartyCat`) the generators
(`PartyGen`) are the party programs `Party.Prog E O α`, denoted by `Prog.toSys`, and the loops
`Prog.loopSys body s₀`, with values in the category of port types `SysCat`; the functor is
`PartyCat.toSys`. In the quantum one (`QPartyCat R`) the generators are the quantum party
programs `QProg R E O α` and their loops, with values in `QSysCat R`; the functor is
`QPartyCat.toQRSys`. The parallel composition `ProgE.par` of programs is the tensor product of
the category (`PartyCat.ofProg_par`, `QPartyCat.ofProg_par`). The party language has no
program-level feedback operation: the trace of the category is the term constructor
`WTerm.trace`, sent to the unbounded loopback of `SysCat` and `QSysCat R`. Port functions need
no generator of their own, since the forwarding party denotes them
(`PartyCat.toSys_map_ofLoop_forward`).

Search words: party language, traced monoidal functor, denotation, compositionality,
wiring diagram, syntactic category.

## Main definitions

* `Party.WTerm.setoid g`: equality of denotations `TracedTerm.WTerm.den g` as a setoid on terms.
* `Party.Diag g`: the category of terms modulo equality of denotations, with
  `MonoidalCategory`, `SymmetricCategory` and `TracedCategory` instances.
* `Party.Diag.functor g`: the denotation functor, with a `Functor.Braided` instance.
* `Party.PartyCat`, `Party.PartyCat.toSys`: party programs and their denotation in `SysCat`.
* `Party.QPartyCat R`, `Party.QPartyCat.toQRSys`: quantum party programs and their denotation
  in `QSysCat R`.

## Main results

* `Party.Diag.map_tensorHom`, `Party.Diag.map_trace`, `Party.Diag.map_associator_hom`,
  `Party.Diag.map_braiding_hom`: the denotation functor is strict monoidal, symmetric and
  traced.
* `Party.Diag.hom_ext`: the denotation functor is faithful.
* `Party.PartyCat.ofProg_par`, `Party.QPartyCat.ofProg_par`: the parallel composition of
  programs is the tensor product.
* `Party.PartyCat.toSys_map_ofLoop_of_act`, `Party.QPartyCat.toQRSys_map_ofLoop_of_act`,
  `Party.PartyCat.toSys_map_ofLoop_forward`: loops of one activation, and port functions as
  forwarding parties.
* `Party.PartyCat.ofProg_eq_iff`: two programs are equal in the category exactly when their
  denotations are step-equivalent.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party

open CategoryTheory MonoidalCategory

universe u v w

open CatCrypt.Category.TracedTerm

namespace WTerm

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [TracedCategory C] {Gen : C → C → Type w}

/-- Equality of denotations as a setoid on terms. -/
def setoid (g : ∀ {X Y : C}, Gen X Y → (X ⟶ Y)) (X Y : C) : Setoid (WTerm Gen X Y) :=
  Setoid.ker (WTerm.den g)

end WTerm

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [TracedCategory C] {Gen : C → C → Type w}

/-- The objects of the category of wiring diagrams over the generators denoted by `g`: the
objects of `C`. -/
structure Diag (g : ∀ {X Y : C}, Gen X Y → (X ⟶ Y)) : Type u where
  /-- The object of `C`. -/
  obj : C

namespace Diag

variable {g : ∀ {X Y : C}, Gen X Y → (X ⟶ Y)}

/-- The category of wiring diagrams: a morphism is a term modulo equality of denotations;
composition is sequence and the identity is the identity term. -/
instance category : Category.{max u w} (Diag g) where
  Hom X Y := Quotient (WTerm.setoid g X.obj Y.obj)
  id X := ⟦.id X.obj⟧
  comp := Quotient.map₂ Term.seq fun _ _ h₁ _ _ h₂ =>
    show _ ≫ _ = _ ≫ _ from congrArg₂ (· ≫ ·) h₁ h₂
  id_comp := by
    rintro X Y ⟨t⟩
    exact Quotient.sound (Category.id_comp (WTerm.den g t))
  comp_id := by
    rintro X Y ⟨t⟩
    exact Quotient.sound (Category.comp_id (WTerm.den g t))
  assoc := by
    rintro W X Y Z ⟨t₁⟩ ⟨t₂⟩ ⟨t₃⟩
    exact Quotient.sound (Category.assoc (WTerm.den g t₁) (WTerm.den g t₂) (WTerm.den g t₃))

variable (g) in
/-- The denotation functor: a class of terms is sent to the common denotation. -/
def functor : Diag g ⥤ C where
  obj X := X.obj
  map f := Quotient.lift (WTerm.den g) (fun _ _ h => h) f
  map_id _ := rfl
  map_comp := by
    rintro X Y Z ⟨t⟩ ⟨t'⟩
    rfl

/-- Unfolding lemma of the denotation functor on objects. -/
@[simp] theorem functor_obj (X : Diag g) : (functor g).obj X = X.obj :=
  rfl

/-- Unfolding lemma of the denotation functor on a class of terms. -/
@[simp] theorem functor_map_mk {X Y : Diag g} (t : WTerm Gen X.obj Y.obj) :
    (functor g).map (⟦t⟧ : X ⟶ Y) = WTerm.den g t :=
  rfl

/-- **Faithfulness.** Morphisms with the same denotation are equal. -/
theorem hom_ext {X Y : Diag g} {f f' : X ⟶ Y} (h : (functor g).map f = (functor g).map f') :
    f = f' := by
  induction f using Quotient.inductionOn
  induction f' using Quotient.inductionOn
  exact Quotient.sound h

/-- The denotation functor is faithful. -/
instance faithful : (functor g).Faithful where
  map_injective h := hom_ext h

/-- The tensor product of morphisms: the tensor of terms. -/
def tensorHom {X₁ Y₁ X₂ Y₂ : Diag g} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    (⟨X₁.obj ⊗ X₂.obj⟩ : Diag g) ⟶ ⟨Y₁.obj ⊗ Y₂.obj⟩ :=
  Quotient.map₂ Term.tensor (fun _ _ h₁ _ _ h₂ =>
    show _ ⊗ₘ _ = _ ⊗ₘ _ from congrArg₂ (· ⊗ₘ ·) h₁ h₂) f₁ f₂

/-- The isomorphism of `Diag g` given by two terms that denote an isomorphism of `C`. -/
def isoOfTerms {X Y : Diag g} (e : X.obj ≅ Y.obj) (t : WTerm Gen X.obj Y.obj)
    (t' : WTerm Gen Y.obj X.obj) (ht : WTerm.den g t = e.hom) (ht' : WTerm.den g t' = e.inv) :
    X ≅ Y where
  hom := ⟦t⟧
  inv := ⟦t'⟧
  hom_inv_id := hom_ext (by simp [ht, ht'])
  inv_hom_id := hom_ext (by simp [ht, ht'])

/-- The monoidal data: the tensor of `C` on objects, the tensor of terms, the unit of `C` and
the structure-map terms. -/
instance monoidalCategoryStruct : MonoidalCategoryStruct (Diag g) where
  tensorObj X Y := ⟨X.obj ⊗ Y.obj⟩
  tensorHom := tensorHom
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight f Y := tensorHom f (𝟙 Y)
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z :=
    isoOfTerms (α_ X.obj Y.obj Z.obj) (.gen (.assoc _ _ _)) (.gen (.assocInv _ _ _)) rfl rfl
  leftUnitor X := isoOfTerms (λ_ X.obj) (.gen (.lunit _)) (.gen (.lunitInv _)) rfl rfl
  rightUnitor X := isoOfTerms (ρ_ X.obj) (.gen (.runit _)) (.gen (.runitInv _)) rfl rfl

/-- Unfolding lemma of the tensor product of objects. -/
@[simp] theorem tensorObj_obj (X Y : Diag g) : (X ⊗ Y).obj = X.obj ⊗ Y.obj :=
  rfl

/-- Unfolding lemma of the unit object. -/
@[simp] theorem tensorUnit_obj : (𝟙_ (Diag g)).obj = 𝟙_ C :=
  rfl

/-- **Strictness on the tensor.** The denotation of a tensor product is the tensor product. -/
@[simp] theorem map_tensorHom {X₁ Y₁ X₂ Y₂ : Diag g} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    (functor g).map (f₁ ⊗ₘ f₂) = (functor g).map f₁ ⊗ₘ (functor g).map f₂ := by
  induction f₁ using Quotient.inductionOn
  induction f₂ using Quotient.inductionOn
  rfl

/-- The denotation of a left whiskering. -/
@[simp] theorem map_whiskerLeft (X : Diag g) {Y Z : Diag g} (f : Y ⟶ Z) :
    (functor g).map (X ◁ f) = (functor g).obj X ◁ (functor g).map f := by
  induction f using Quotient.inductionOn
  exact id_tensorHom _ _

/-- The denotation of a right whiskering. -/
@[simp] theorem map_whiskerRight {X Y : Diag g} (f : X ⟶ Y) (Z : Diag g) :
    (functor g).map (f ▷ Z) = (functor g).map f ▷ (functor g).obj Z := by
  induction f using Quotient.inductionOn
  exact tensorHom_id _ _

/-- The denotation of the associator. -/
@[simp] theorem map_associator_hom (X Y Z : Diag g) :
    (functor g).map (α_ X Y Z).hom = (α_ X.obj Y.obj Z.obj).hom :=
  rfl

/-- The denotation of the inverse associator. -/
@[simp] theorem map_associator_inv (X Y Z : Diag g) :
    (functor g).map (α_ X Y Z).inv = (α_ X.obj Y.obj Z.obj).inv :=
  rfl

/-- The denotation of the left unitor. -/
@[simp] theorem map_leftUnitor_hom (X : Diag g) :
    (functor g).map (λ_ X).hom = (λ_ X.obj).hom :=
  rfl

/-- The denotation of the inverse left unitor. -/
@[simp] theorem map_leftUnitor_inv (X : Diag g) :
    (functor g).map (λ_ X).inv = (λ_ X.obj).inv :=
  rfl

/-- The denotation of the right unitor. -/
@[simp] theorem map_rightUnitor_hom (X : Diag g) :
    (functor g).map (ρ_ X).hom = (ρ_ X.obj).hom :=
  rfl

/-- The denotation of the inverse right unitor. -/
@[simp] theorem map_rightUnitor_inv (X : Diag g) :
    (functor g).map (ρ_ X).inv = (ρ_ X.obj).inv :=
  rfl

/-- The category of wiring diagrams is monoidal; each law is the law of `C` on denotations. -/
instance monoidalCategory : MonoidalCategory (Diag g) where
  tensorHom_def f₁ f₂ := hom_ext (by
    simp only [map_tensorHom, Functor.map_comp, map_whiskerRight, map_whiskerLeft]
    exact tensorHom_def _ _)
  id_tensorHom_id X Y := hom_ext (by simp)
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := hom_ext (by
    simp only [map_tensorHom, Functor.map_comp]
    exact tensorHom_comp_tensorHom _ _ _ _)
  whiskerLeft_id X Y := hom_ext (by simp)
  id_whiskerRight X Y := hom_ext (by simp)
  associator_naturality f₁ f₂ f₃ := hom_ext (by
    simp only [map_tensorHom, Functor.map_comp, map_associator_hom]
    exact associator_naturality _ _ _)
  leftUnitor_naturality f := hom_ext (by
    simp only [Functor.map_comp, map_whiskerLeft, map_leftUnitor_hom]
    exact leftUnitor_naturality _)
  rightUnitor_naturality f := hom_ext (by
    simp only [Functor.map_comp, map_whiskerRight, map_rightUnitor_hom]
    exact rightUnitor_naturality _)
  pentagon W X Y Z := hom_ext (by simp)
  triangle X Y := hom_ext (by simp)

/-- The symmetry of the category of wiring diagrams: the symmetry term. -/
def braiding (X Y : Diag g) : X ⊗ Y ≅ Y ⊗ X :=
  isoOfTerms (X := X ⊗ Y) (Y := Y ⊗ X) (β_ X.obj Y.obj) (.gen (.braid _ _))
    (.gen (.braid _ _)) rfl
    (SymmetricCategory.braiding_swap_eq_inv_braiding X.obj Y.obj)

/-- Unfolding lemma of the denotation of the symmetry. -/
theorem map_braiding_hom' (X Y : Diag g) :
    (functor g).map (braiding X Y).hom = (β_ X.obj Y.obj).hom :=
  rfl

/-- Unfolding lemma of the denotation of the inverse symmetry. -/
theorem map_braiding_inv' (X Y : Diag g) :
    (functor g).map (braiding X Y).inv = (β_ X.obj Y.obj).inv :=
  SymmetricCategory.braiding_swap_eq_inv_braiding X.obj Y.obj

/-- The category of wiring diagrams is symmetric monoidal. -/
instance symmetricCategory : SymmetricCategory (Diag g) where
  braiding := braiding
  braiding_naturality_right X Y Z f := hom_ext (by
    simp only [Functor.map_comp, map_whiskerLeft, map_whiskerRight, map_braiding_hom']
    exact BraidedCategory.braiding_naturality_right _ _)
  braiding_naturality_left f Z := hom_ext (by
    simp only [Functor.map_comp, map_whiskerLeft, map_whiskerRight, map_braiding_hom']
    exact BraidedCategory.braiding_naturality_left _ _)
  hexagon_forward X Y Z := hom_ext (by simp [map_braiding_hom'])
  hexagon_reverse X Y Z := hom_ext (by simp [map_braiding_hom'])
  symmetry X Y := hom_ext (by simp [map_braiding_hom'])

/-- The denotation of the symmetry. -/
@[simp] theorem map_braiding_hom (X Y : Diag g) :
    (functor g).map (β_ X Y).hom = (β_ X.obj Y.obj).hom :=
  rfl

/-- The trace of the category of wiring diagrams: the trace term. -/
def trace (U : Diag g) {X Y : Diag g} (f : X ⊗ U ⟶ Y ⊗ U) : X ⟶ Y :=
  Quotient.map (WTerm.traceAlong U.obj) (fun _ _ h =>
    show TracedCategory.trace _ _ = TracedCategory.trace _ _ from
      congrArg (TracedCategory.trace U.obj) h) f

/-- **Strictness on the trace.** The denotation of a trace is the trace of the denotation. -/
@[simp] theorem map_trace (U : Diag g) {X Y : Diag g} (f : X ⊗ U ⟶ Y ⊗ U) :
    (functor g).map (trace U f) = TracedCategory.trace U.obj ((functor g).map f) := by
  induction f using Quotient.inductionOn
  rfl

/-- The category of wiring diagrams is traced; each axiom is the axiom of `C` on
denotations. -/
instance tracedCategory : TracedCategory (Diag g) where
  trace := trace
  trace_whiskerRight_comp U _ _ _ f₁ f₂ := hom_ext (by
    simp only [map_trace, Functor.map_comp, map_whiskerRight]
    exact TracedCategory.trace_whiskerRight_comp _ _ _)
  trace_comp_whiskerRight U _ _ _ f₁ f₂ := hom_ext (by
    simp only [map_trace, Functor.map_comp, map_whiskerRight]
    exact TracedCategory.trace_comp_whiskerRight _ _ _)
  trace_whiskerLeft_comp f₁ f₂ := hom_ext (by
    simp only [map_trace, Functor.map_comp, map_whiskerLeft]
    exact TracedCategory.trace_whiskerLeft_comp _ _)
  trace_tensorUnit f := hom_ext (by
    simp only [map_trace, Functor.map_comp, map_rightUnitor_inv, map_rightUnitor_hom]
    exact TracedCategory.trace_tensorUnit _)
  trace_tensor U V _ _ f := hom_ext (by
    simp only [map_trace, Functor.map_comp, map_associator_hom, map_associator_inv]
    exact TracedCategory.trace_tensor _ _ _)
  whiskerLeft_trace W U _ _ f := hom_ext (by
    simp only [map_whiskerLeft, map_trace, Functor.map_comp, map_associator_hom,
      map_associator_inv]
    exact TracedCategory.whiskerLeft_trace _ _ _)
  trace_braiding U := hom_ext (by simp)

/-- The denotation functor is strict monoidal: the tensorator and the unit are identities. -/
def functorCoreMonoidal : (functor g).CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left f X' := by simp
  μIso_hom_natural_right X' f := by simp
  associativity X Y Z := by simp
  left_unitality X := by simp
  right_unitality X := by simp

/-- The denotation functor is monoidal, with identity tensorator and unit. -/
instance functorMonoidal : (functor g).Monoidal :=
  functorCoreMonoidal.toMonoidal

/-- The tensorator of the denotation functor is the identity. -/
@[simp] theorem functor_μ (X Y : Diag g) :
    Functor.LaxMonoidal.μ (functor g) X Y = 𝟙 (X.obj ⊗ Y.obj) :=
  rfl

/-- **The denotation functor is a strict symmetric monoidal functor.** -/
instance functorBraided : (functor g).Braided where
  braided X Y := by simp

end Diag

/-! ## Classical party programs -/

section Classical

open CatCrypt.Core CatCrypt.Crypto.UCTransparent

/-- The generators of the category of party programs: a party program and the loop of a party
program, on the ports of their events and outputs. -/
inductive PartyGen (X Y : SysCat) : Type 1 where
  /-- A party program. -/
  | prog {α : Type} (p : Prog X.P Y.P α)
  /-- The loop of the body `body` from the state `s₀`. -/
  | loop {σ : Type} (body : σ → Prog X.P Y.P σ) (s₀ : σ)

/-- The denotation of a generator: the class of `Prog.toSys p` or of `Prog.loopSys body s₀`. -/
noncomputable def PartyGen.den {X Y : SysCat} : PartyGen X Y → (X ⟶ Y)
  | .prog p => ⟦⟨_, Prog.toSys p⟩⟧
  | .loop body s₀ => ⟦⟨_, Prog.loopSys body s₀⟩⟧

/-- **The category of party programs**: wiring diagrams of party programs and their loops,
modulo step equivalence of the systems they denote. -/
abbrev PartyCat : Type 1 :=
  Diag (C := SysCat) fun {X Y} => @PartyGen.den X Y

namespace PartyCat

variable {E O E' O' α β σ : Type}

/-- **The denotation of party programs** as a strict traced symmetric monoidal functor into
the category of port types. -/
noncomputable abbrev toSys : PartyCat ⥤ SysCat :=
  Diag.functor _

/-- The object of the ports `E`. -/
abbrev port (E : Type) : PartyCat :=
  ⟨⟨E⟩⟩

/-- The morphism of a party program. -/
noncomputable def ofProg (p : Prog E O α) : port E ⟶ port O :=
  ⟦WTerm.ofGen (.prog p)⟧

/-- The morphism of the loop of a party program. -/
noncomputable def ofLoop (body : σ → Prog E O σ) (s₀ : σ) : port E ⟶ port O :=
  ⟦WTerm.ofGen (.loop body s₀)⟧

/-- Unfolding lemma of `toSys` at a program. -/
@[simp] theorem toSys_map_ofProg (p : Prog E O α) :
    toSys.map (ofProg p) = ⟦⟨_, Prog.toSys p⟩⟧ :=
  rfl

/-- Unfolding lemma of `toSys` at a loop. -/
@[simp] theorem toSys_map_ofLoop (body : σ → Prog E O σ) (s₀ : σ) :
    toSys.map (ofLoop body s₀) = ⟦⟨_, Prog.loopSys body s₀⟩⟧ :=
  rfl

/-- Two morphisms of party programs are equal exactly when their denotations are. -/
theorem hom_eq_iff {X Y : PartyCat} (f f' : X ⟶ Y) : f = f' ↔ toSys.map f = toSys.map f' :=
  ⟨fun h => h ▸ rfl, Diag.hom_ext⟩

/-- Two party programs are equal in the category exactly when their denotations are
step-equivalent. -/
theorem ofProg_eq_iff (p p' : Prog E O α) :
    ofProg p = ofProg p' ↔ Sys.StepEq ⟨_, Prog.toSys p⟩ ⟨_, Prog.toSys p'⟩ := by
  rw [hom_eq_iff, toSys_map_ofProg, toSys_map_ofProg]
  exact Quotient.eq

/-- **The parallel composition of programs is the tensor product.** -/
theorem ofProg_par (p : Prog E O α) (q : Prog E' O' β) :
    ofProg (ProgE.par p q) = ofProg p ⊗ₘ ofProg q :=
  Diag.hom_ext (by
    rw [Diag.map_tensorHom]
    exact Quotient.sound (Prog.toSys_par p q))

/-- **Loops of one activation.** When every iteration of `body` is one activation, the
denotation of the loop is the class of the system with the iteration as its step. -/
theorem toSys_map_ofLoop_of_act (body : σ → Prog E O σ) (s₀ : σ)
    (step : σ → E → SPComp (σ × O))
    (h : ∀ s e, Prog.act (body s) e = SPComp.map (fun q => (Prog.ret q.1, q.2)) (step s e)) :
    toSys.map (ofLoop body s₀) = ⟦⟨σ, ⟨s₀, step⟩⟩⟧ :=
  Quotient.sound (Prog.loopSys_stepEq body s₀ step h)

/-- **Port functions are party programs.** The loop of the forwarding party for `f` denotes the
morphism of `f`. -/
theorem toSys_map_ofLoop_forward (f : E → O) :
    toSys.map (ofLoop (fun _ => Prog.forward f) ()) =
      SysCat.homOfFun (X := ⟨E⟩) (Y := ⟨O⟩) f :=
  Quotient.sound (Prog.forward_stepEq f)

end PartyCat

end Classical

/-! ## Quantum party programs -/

section Quantum

open CatCrypt.Quantum.ReactiveUC

variable (R : Type) [Fintype R]

/-- The generators of the category of quantum party programs on the register `R`: a quantum
party program and the loop of one. -/
inductive QPartyGen (X Y : QSysCat R) : Type 1 where
  /-- A quantum party program. -/
  | prog {α : Type} (p : QProg R X.P Y.P α)
  /-- The loop of the body `body` from the state `s₀`. -/
  | loop {σ : Type} (body : σ → QProg R X.P Y.P σ) (s₀ : σ)

variable {R}

/-- The denotation of a generator: the class of `QProg.toQRSys p` or of
`QProg.loopQSys body s₀`. -/
noncomputable def QPartyGen.den {X Y : QSysCat R} : QPartyGen R X Y → (X ⟶ Y)
  | .prog p => ⟦⟨_, QProg.toQRSys p⟩⟧
  | .loop body s₀ => ⟦⟨_, QProg.loopQSys body s₀⟩⟧

variable (R) in
/-- **The category of quantum party programs** on the register `R`: wiring diagrams of
quantum party programs and their loops, modulo step equivalence of the quantum reactive
systems they denote. -/
abbrev QPartyCat : Type 1 :=
  Diag (C := QSysCat R) fun {X Y} => @QPartyGen.den R _ X Y

namespace QPartyCat

variable {E O E' O' α β σ : Type}

variable (R) in
/-- **The denotation of quantum party programs** as a strict traced symmetric monoidal functor
into `QSysCat R`. -/
noncomputable abbrev toQRSys : QPartyCat R ⥤ QSysCat R :=
  Diag.functor _

variable (R) in
/-- The object of the ports `E`. -/
abbrev port (E : Type) : QPartyCat R :=
  ⟨⟨E⟩⟩

/-- The morphism of a quantum party program. -/
noncomputable def ofProg (p : QProg R E O α) : port R E ⟶ port R O :=
  ⟦WTerm.ofGen (.prog p)⟧

/-- The morphism of the loop of a quantum party program. -/
noncomputable def ofLoop (body : σ → QProg R E O σ) (s₀ : σ) : port R E ⟶ port R O :=
  ⟦WTerm.ofGen (.loop body s₀)⟧

/-- Unfolding lemma of `toQRSys` at a program. -/
@[simp] theorem toQRSys_map_ofProg (p : QProg R E O α) :
    (toQRSys R).map (ofProg p) = ⟦⟨_, QProg.toQRSys p⟩⟧ :=
  rfl

/-- Unfolding lemma of `toQRSys` at a loop. -/
@[simp] theorem toQRSys_map_ofLoop (body : σ → QProg R E O σ) (s₀ : σ) :
    (toQRSys R).map (ofLoop body s₀) = ⟦⟨_, QProg.loopQSys body s₀⟩⟧ :=
  rfl

/-- Two morphisms of quantum party programs are equal exactly when their denotations are. -/
theorem hom_eq_iff {X Y : QPartyCat R} (f f' : X ⟶ Y) :
    f = f' ↔ (toQRSys R).map f = (toQRSys R).map f' :=
  ⟨fun h => h ▸ rfl, Diag.hom_ext⟩

/-- **The parallel composition of quantum programs is the tensor product.** -/
theorem ofProg_par (p : QProg R E O α) (q : QProg R E' O' β) :
    ofProg (ProgE.par p q) = ofProg p ⊗ₘ ofProg q :=
  Diag.hom_ext (by
    rw [Diag.map_tensorHom]
    exact Quotient.sound (QProg.toQRSys_par p q))

/-- **Loops of one activation.** When every iteration of `body` is one activation, the
denotation of the loop is the class of the system with the iteration as its step. -/
theorem toQRSys_map_ofLoop_of_act (body : σ → QProg R E O σ) (s₀ : σ)
    (step : σ → E → _root_.Quantum.SubInstrument R R (σ × O))
    (h : ∀ s e, QProg.act (body s) e =
      (step s e).bind fun q => _root_.Quantum.SubInstrument.pure (ProgE.ret q.1, q.2)) :
    (toQRSys R).map (ofLoop body s₀) = ⟦⟨σ, ⟨s₀, step⟩⟩⟧ :=
  Quotient.sound (QProg.loopQSys_stepEq body s₀ step h)

end QPartyCat

end Quantum

end CatCrypt.Crypto.Party
