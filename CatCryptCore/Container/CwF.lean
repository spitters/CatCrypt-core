/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import PolyFun.PFunctor.Lens.Basic

/-!
# The category with families of containers over `Type`

This module gives the polynomial model of type theory, in the form of Cavallo and Höfer (§3), who
follow Kovács's formalization of a version of von Glehn's construction, with base model `Type u`.

A context is a container `Γ = (Γ.A, Γ.B)`, a `PFunctor`, and a substitution `Δ → Γ` is a
`PFunctor.Lens`. A type over `Γ` (`Ty`) has shapes `S γ` and positions `P γ s`. A term (`Tm`) has
a shape `S γ` at each shape of the context and sends a position of that shape back to a position of
the context. Context extension (`ext`) has shapes `Σ γ, S γ` and positions `Γ.B γ ⊕ P γ s`.

Which laws are strict. A law proved by `rfl` holds by definitional unfolding, which includes the
structure η of `Ty`, `Tm`, `Lens` and `Sigma`:

* strict: the category laws of lenses (`lens_id_comp`, `lens_comp_id`, `lens_comp_assoc`), the
  substitution laws of types and terms (`Ty.sub_id`, `Ty.sub_comp`, `Tm.sub_id`, `Tm.sub_comp`),
  the projection laws of context extension (`wk_extend`, `var_sub_extend`), the stability of
  `Ty.sigma`, `Ty.eq`, `Ty.coprod`, `Ty.modal`, the β laws of `Ty.sigma`, `Tm.J` and `Tm.case`;
* propositional: every law that compares two maps out of a sum of positions or out of the empty
  type (`extend_wk_var`, `extend_comp`, `toUnit_unique`, `Tm.mkPair_fst_snd`, `Tm.mkPair_sub`,
  `Tm.J_sub`, `Tm.case_eta`, `Tm.case_sub`). The base `Type` has no strict η for coproducts, so
  these hold by `funext` and a case split, where the paper has strict equalities.

Identity types follow Remark 3.9 of Cavallo and Höfer: the shapes of `u = v` are the paths between
the shapes of `u` and `v`, and the positions are empty. A path in the model compares shapes only
(`nonempty_tm_eq_iff`). The base has uniqueness of identity proofs, so the model is one of `ITT`
with that principle.

The functor `Γ ↦ Γ.A` has the fully faithful right adjoint `disc`, with empty positions
(`discHomEquiv`, `discDiscEquiv`, Lemma 3.15), and `Ty.modal` is the induced dependent right adjoint
(`Tm.modalEquiv`, Corollary 3.16). The identity type is modal by definition.

The dependent product and the Diller–Nahm predicate are in `CatCryptCore.Container.CwFPi`.

## Main definitions

* `Ty`, `Tm`, `Ty.sub`, `Tm.sub`, `Tm.toSection`, `Tm.ofSection` — types, terms, substitution;
* `unit`, `toUnit`, `ext`, `wk`, `var`, `extend`, `inst`, `lift` — the substitution calculus;
* `Ty.sigma`, `Tm.mkPair`, `Tm.fst`, `Tm.snd` — dependent sums (Proposition 3.7);
* `PathT`, `Ty.eq`, `Tm.refl`, `Tm.J` — identity types (Proposition 3.8);
* `Ty.empty`, `Ty.coprod`, `Tm.inl`, `Tm.inr`, `Tm.case`, `Tm.emptyElim` — coproducts
  (Proposition 3.13);
* `disc`, `discUnit`, `Ty.modal`, `Tm.toModal` — the reflective modality.

## Main results

* `wk_extend`, `var_sub_extend`, `extend_wk_var`, `extend_comp` — Proposition 3.6;
* `Tm.fst_mkPair`, `Tm.snd_mkPair`, `Tm.mkPair_fst_snd` — β and η of dependent sums;
* `Tm.J_refl`, `Tm.J_sub`, `nonempty_tm_eq_iff` — the eliminator of paths, and paths as equal
  shapes;
* `Tm.case_inl`, `Tm.case_inr`, `Tm.case_eta` — β and η of coproducts;
* `discHomEquiv`, `discDiscEquiv`, `extDiscLens_comp_inv`, `extDiscInv_comp_lens`, `Tm.modalEquiv` —
  the adjunction, its full faithfulness, and the preservation of context extension.

## References

* T. von Glehn, *Polynomials and models of type theory*, PhD thesis, Cambridge, 2015;
* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018;
* E. Cavallo, T. Höfer, *Univalence without function extensionality*, arXiv:2605.00812, §3;
* T. Altenkirch, A. Kaposi, *Type theory in type theory using quotient inductive types*, POPL 2016.

Search words: category with families, CwF, polynomial model, container model, natural model,
context extension, substitution calculus, dependent sum, identity type, coproduct, modality,
reflective subcategory, dependent right adjoint.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container.CwF

open PFunctor

/-- A context of the model: a container with shapes and positions in `Type u`. -/
abbrev Ctx := PFunctor.{u, u}

/-! ## The category of contexts -/

section Category

variable {Γ Δ Θ Ξ : Ctx.{u}}

/-- The identity substitution is a left unit, strictly. -/
theorem lens_id_comp (σ : Lens Δ Γ) : Lens.comp (Lens.id Γ) σ = σ := rfl

/-- The identity substitution is a right unit, strictly. -/
theorem lens_comp_id (σ : Lens Δ Γ) : Lens.comp σ (Lens.id Δ) = σ := rfl

/-- The composition of substitutions is associative, strictly. -/
theorem lens_comp_assoc (σ : Lens Δ Γ) (τ : Lens Θ Δ) (ρ : Lens Ξ Θ) :
    Lens.comp (Lens.comp σ τ) ρ = Lens.comp σ (Lens.comp τ ρ) := rfl

end Category

/-! ## Types and terms -/

/-- A type over the context `Γ`: shapes over the shapes of `Γ`, and positions over those. -/
structure Ty (Γ : Ctx.{u}) : Type (u + 1) where
  /-- The shapes of the type at a shape of the context. -/
  S : Γ.A → Type u
  /-- The positions of the type at a shape of the type. -/
  P : ∀ γ, S γ → Type u

/-- A term of the type `A` in the context `Γ`: a shape of `A` at each shape of `Γ`, and a backward
map from the positions of that shape to the positions of `Γ`. -/
structure Tm (Γ : Ctx.{u}) (A : Ty Γ) : Type u where
  /-- The shape of the term at a shape of the context. -/
  S : ∀ γ, A.S γ
  /-- The backward map on positions. -/
  P : ∀ γ, A.P γ (S γ) → Γ.B γ

section Basic

variable {Γ Δ Θ : Ctx.{u}}

/-- The substitution of a type: reindexing along the forward map. -/
def Ty.sub (A : Ty Γ) (σ : Lens Δ Γ) : Ty Δ where
  S d := A.S (σ.toFunA d)
  P d := A.P (σ.toFunA d)

/-- The substitution of a term: the shape is reindexed along the forward map, and a position is sent
back through the term and then through the substitution. -/
def Tm.sub {A : Ty Γ} (a : Tm Γ A) (σ : Lens Δ Γ) : Tm Δ (A.sub σ) where
  S d := a.S (σ.toFunA d)
  P d x := σ.toFunB d (a.P (σ.toFunA d) x)

/-- Types are stable under the identity substitution, strictly. -/
theorem Ty.sub_id (A : Ty Γ) : A.sub (Lens.id Γ) = A := rfl

/-- Types are stable under composition of substitutions, strictly. -/
theorem Ty.sub_comp (A : Ty Γ) (τ : Lens Δ Γ) (σ : Lens Θ Δ) :
    A.sub (Lens.comp τ σ) = (A.sub τ).sub σ := rfl

/-- Terms are stable under the identity substitution, strictly. -/
theorem Tm.sub_id {A : Ty Γ} (a : Tm Γ A) : (a.sub (Lens.id Γ) : Tm Γ A) = a := rfl

/-- Terms are stable under composition of substitutions, strictly. -/
theorem Tm.sub_comp {A : Ty Γ} (a : Tm Γ A) (τ : Lens Δ Γ) (σ : Lens Θ Δ) :
    (a.sub (Lens.comp τ σ) : Tm Θ ((A.sub τ).sub σ)) = (a.sub τ).sub σ := rfl

/-- A term as a section: a shape of the type with its backward map, at each shape of the context. -/
def Tm.toSection {A : Ty Γ} (a : Tm Γ A) : ∀ γ, Σ s : A.S γ, (A.P γ s → Γ.B γ) :=
  fun γ => ⟨a.S γ, a.P γ⟩

/-- The term of a section. -/
def Tm.ofSection {A : Ty Γ} (f : ∀ γ, Σ s : A.S γ, (A.P γ s → Γ.B γ)) : Tm Γ A where
  S γ := (f γ).1
  P γ := (f γ).2

/-- Two terms are equal when their sections are pointwise equal. -/
theorem Tm.ext_section {A : Ty Γ} {a b : Tm Γ A} (h : ∀ γ, a.toSection γ = b.toSection γ) :
    a = b :=
  congrArg Tm.ofSection (funext h)

/-- Two terms with the same shapes are equal when their backward maps are pointwise equal. -/
theorem Tm.congr_P {A : Ty Γ} {S : ∀ γ, A.S γ} {P P' : ∀ γ, A.P γ (S γ) → Γ.B γ}
    (h : ∀ γ x, P γ x = P' γ x) : (Tm.mk S P : Tm Γ A) = Tm.mk S P' :=
  congrArg (Tm.mk S) (funext fun γ => funext (h γ))

end Basic

/-! ## The substitution calculus -/

/-- The empty context: one shape and no positions. -/
abbrev unit : Ctx.{u} := ⟨PUnit, fun _ => PEmpty⟩

/-- The extension of a context by a type: shapes are pairs, and positions are the positions of the
context or those of the type (Proposition 3.6). -/
abbrev ext (Γ : Ctx.{u}) (A : Ty Γ) : Ctx.{u} :=
  ⟨Σ γ, A.S γ, fun x => Γ.B x.1 ⊕ A.P x.1 x.2⟩

section Calculus

variable {Γ Δ Θ : Ctx.{u}} {A : Ty Γ}

/-- The unique substitution into the empty context. -/
def toUnit (Γ : Ctx.{u}) : Lens Γ unit where
  toFunA _ := PUnit.unit
  toFunB _ e := e.elim

/-- The empty context is terminal. The backward map out of the empty type is unique by `funext`. -/
theorem toUnit_unique (σ : Lens Γ unit) : σ = toUnit Γ :=
  congrArg (Lens.mk _) (funext fun _ => funext fun e => e.elim)

/-- The projection from a context extension. -/
def wk (A : Ty Γ) : Lens (ext Γ A) Γ where
  toFunA x := x.1
  toFunB _ d := Sum.inl d

/-- The variable of a context extension. -/
def var (A : Ty Γ) : Tm (ext Γ A) (A.sub (wk A)) where
  S x := x.2
  P _ y := Sum.inr y

/-- The substitution into a context extension: on shapes the pair, on positions the copairing. -/
def extend (σ : Lens Δ Γ) (a : Tm Δ (A.sub σ)) : Lens Δ (ext Γ A) where
  toFunA d := ⟨σ.toFunA d, a.S d⟩
  toFunB d := Sum.elim (σ.toFunB d) (a.P d)

/-- The substitution of a term for the last variable. -/
abbrev inst (a : Tm Γ A) : Lens Γ (ext Γ A) := extend (Lens.id Γ) a

/-- The weakening of a substitution under a binder. -/
abbrev lift (σ : Lens Δ Γ) (A : Ty Γ) : Lens (ext Δ (A.sub σ)) (ext Γ A) :=
  extend (Lens.comp σ (wk (A.sub σ))) (var (A.sub σ))

/-- The projection after an extension is the original substitution, strictly. -/
theorem wk_extend (σ : Lens Δ Γ) (a : Tm Δ (A.sub σ)) :
    Lens.comp (wk A) (extend σ a) = σ := rfl

/-- The variable under an extension is the original term, strictly. -/
theorem var_sub_extend (σ : Lens Δ Γ) (a : Tm Δ (A.sub σ)) :
    ((var A).sub (extend σ a) : Tm Δ (A.sub σ)) = a := rfl

/-- The extension of the projection by the variable is the identity. This is the η law of the sum of
positions. -/
theorem extend_wk_var (A : Ty Γ) : extend (wk A) (var A) = Lens.id (ext Γ A) :=
  congrArg (Lens.mk _) (funext fun _ => funext fun y => by cases y <;> rfl)

/-- Extension is natural in the domain. This is the η law of the sum of positions. -/
theorem extend_comp (σ : Lens Δ Γ) (a : Tm Δ (A.sub σ)) (τ : Lens Θ Δ) :
    Lens.comp (extend σ a) τ = extend (Lens.comp σ τ) (a.sub τ) :=
  congrArg (Lens.mk _) (funext fun _ => funext fun y => by cases y <;> rfl)

end Calculus

/-! ## Dependent sums -/

section Sigma

variable {Γ Δ : Ctx.{u}} {A : Ty Γ} {B : Ty (ext Γ A)}

/-- The dependent sum: shapes are pairs and positions are a position of either component
(Proposition 3.7). -/
def Ty.sigma (A : Ty Γ) (B : Ty (ext Γ A)) : Ty Γ where
  S γ := Σ a : A.S γ, B.S ⟨γ, a⟩
  P γ x := A.P γ x.1 ⊕ B.P ⟨γ, x.1⟩ x.2

/-- The dependent sum is stable under substitution, strictly. -/
theorem Ty.sigma_sub (A : Ty Γ) (B : Ty (ext Γ A)) (σ : Lens Δ Γ) :
    (Ty.sigma A B).sub σ = Ty.sigma (A.sub σ) (B.sub (lift σ A)) := rfl

/-- The pairing of terms. -/
def Tm.mkPair (a : Tm Γ A) (b : Tm Γ (B.sub (inst a))) : Tm Γ (Ty.sigma A B) where
  S γ := ⟨a.S γ, b.S γ⟩
  P γ := Sum.elim (a.P γ) (b.P γ)

/-- The first projection. -/
def Tm.fst (t : Tm Γ (Ty.sigma A B)) : Tm Γ A where
  S γ := (t.S γ).1
  P γ x := t.P γ (Sum.inl x)

/-- The second projection. -/
def Tm.snd (t : Tm Γ (Ty.sigma A B)) : Tm Γ (B.sub (inst (Tm.fst t))) where
  S γ := (t.S γ).2
  P γ y := t.P γ (Sum.inr y)

/-- The first projection of a pair, strictly. -/
theorem Tm.fst_mkPair (a : Tm Γ A) (b : Tm Γ (B.sub (inst a))) : Tm.fst (Tm.mkPair a b) = a := rfl

/-- The second projection of a pair, strictly. -/
theorem Tm.snd_mkPair (a : Tm Γ A) (b : Tm Γ (B.sub (inst a))) :
    (Tm.snd (Tm.mkPair a b) : Tm Γ (B.sub (inst a))) = b := rfl

/-- A term of a dependent sum is the pair of its projections. This is the η law of the sum of
positions. -/
theorem Tm.mkPair_fst_snd (t : Tm Γ (Ty.sigma A B)) : Tm.mkPair (Tm.fst t) (Tm.snd t) = t :=
  Tm.congr_P fun _ x => by cases x <;> rfl

/-- The first projection is stable under substitution, strictly. -/
theorem Tm.fst_sub (t : Tm Γ (Ty.sigma A B)) (σ : Lens Δ Γ) :
    (Tm.fst t).sub σ = Tm.fst (B := B.sub (lift σ A)) (t.sub σ) := rfl

/-- The pairing is stable under substitution. This is the η law of the sum of positions. -/
theorem Tm.mkPair_sub (a : Tm Γ A) (b : Tm Γ (B.sub (inst a))) (σ : Lens Δ Γ) :
    (Tm.mkPair a b).sub σ = Tm.mkPair (B := B.sub (lift σ A)) (a.sub σ) (b.sub σ) :=
  Tm.congr_P fun _ x => by cases x <;> rfl

end Sigma

/-! ## The reflective modality -/

/-- The context with shapes `X` and no positions. -/
abbrev disc (X : Type u) : Ctx.{u} := ⟨X, fun _ => PEmpty⟩

section Modal

variable {Γ Δ : Ctx.{u}} {X Y : Type u}

/-- The unit of the reflection: the identity on shapes. -/
def discUnit (Γ : Ctx.{u}) : Lens Γ (disc Γ.A) where
  toFunA γ := γ
  toFunB _ e := e.elim

/-- The functor `disc` on maps of shapes. -/
def discMap (f : X → Y) : Lens (disc X) (disc Y) where
  toFunA := f
  toFunB _ e := e.elim

/-- **The reflection.** A substitution into a context without positions is a map of shapes. -/
def discHomEquiv : Lens Δ (disc X) ≃ (Δ.A → X) where
  toFun σ := σ.toFunA
  invFun f := ⟨f, fun _ e => e.elim⟩
  left_inv _ := congrArg (Lens.mk _) (funext fun _ => funext fun e => e.elim)
  right_inv _ := rfl

/-- The inverse of the reflection is the unit followed by `disc` of the map. -/
theorem discHomEquiv_symm_eq (f : Δ.A → X) :
    discHomEquiv.symm f = Lens.comp (discMap f) (discUnit Δ) :=
  congrArg (Lens.mk _) (funext fun _ => funext fun e => e.elim)

/-- The reflection is natural in the domain. -/
theorem discHomEquiv_comp (σ : Lens Δ (disc X)) (τ : Lens Γ Δ) :
    discHomEquiv (Lens.comp σ τ) = discHomEquiv σ ∘ τ.toFunA := rfl

/-- **`disc` is fully faithful.** Substitutions between contexts without positions are maps of
shapes. -/
def discDiscEquiv : Lens (disc X) (disc Y) ≃ (X → Y) := discHomEquiv

/-- The type with shapes `F` and no positions (Corollary 3.16). -/
def Ty.modal (F : Γ.A → Type u) : Ty Γ where
  S := F
  P _ _ := PEmpty

/-- The modal type is stable under substitution, strictly. -/
theorem Ty.modal_sub (F : Γ.A → Type u) (σ : Lens Δ Γ) :
    (Ty.modal F).sub σ = Ty.modal fun d => F (σ.toFunA d) := rfl

/-- **The dependent right adjoint.** A term of a modal type is a section of its shapes. -/
def Tm.modalEquiv {F : Γ.A → Type u} : Tm Γ (Ty.modal F) ≃ ∀ γ, F γ where
  toFun a := a.S
  invFun s := ⟨s, fun _ e => e.elim⟩
  left_inv _ := Tm.congr_P fun _ e => e.elim
  right_inv _ := rfl

/-- The unit of the modality at a type: a term keeps its shapes and forgets its backward map. -/
def Tm.toModal {A : Ty Γ} (a : Tm Γ A) : Tm Γ (Ty.modal A.S) :=
  Tm.modalEquiv.symm a.S

/-- The comparison of a context extension of a discrete context with a discrete context: the sum of
two empty types of positions is sent to the empty type. -/
def extDiscLens (F : X → Type u) : Lens (ext (disc X) (Ty.modal F)) (disc (Σ x, F x)) where
  toFunA x := x
  toFunB _ e := e.elim

/-- The inverse of `extDiscLens`. -/
def extDiscInv (F : X → Type u) : Lens (disc (Σ x, F x)) (ext (disc X) (Ty.modal F)) where
  toFunA x := x
  toFunB _ y := by
    rcases y with e | e <;> exact e.elim

/-- One composite of the comparison of context extensions is the identity. -/
theorem extDiscLens_comp_inv (F : X → Type u) :
    Lens.comp (extDiscLens F) (extDiscInv F) = Lens.id _ :=
  congrArg (Lens.mk _) (funext fun _ => funext fun e => e.elim)

/-- The other composite of the comparison of context extensions is the identity. -/
theorem extDiscInv_comp_lens (F : X → Type u) :
    Lens.comp (extDiscInv F) (extDiscLens F) = Lens.id _ :=
  congrArg (Lens.mk _) (funext fun _ => funext fun y => by rcases y with e | e <;> exact e.elim)

end Modal

/-! ## Identity types -/

/-- The paths between two elements of a type, in the same universe. -/
abbrev PathT {α : Type u} (a b : α) : Type u := ULift.{u} (PLift (a = b))

/-- The reflexive path. -/
abbrev PathT.refl {α : Type u} (a : α) : PathT a a := ⟨⟨rfl⟩⟩

/-- The identity elimination at a point, on a shape together with its backward map: path induction
transports the positions of the target to those of the base (Proposition 3.8). -/
def jPoint {α : Type u} {a : α} (F : ∀ b, PathT a b → Type u) (G : ∀ b e, F b e → Type u)
    {X : Type u} (wS : F a (PathT.refl a)) (wP : G a (PathT.refl a) wS → X) :
    ∀ (b : α) (e : PathT a b), Σ s : F b e, (G b e s → X)
  | _, ⟨⟨rfl⟩⟩ => ⟨wS, wP⟩

/-- `jPoint` is natural in the target of the backward map. -/
theorem jPoint_map {α : Type u} {a : α} (F : ∀ b, PathT a b → Type u)
    (G : ∀ b e, F b e → Type u) {X Y : Type u} (k : X → Y) (wS : F a (PathT.refl a))
    (wP : G a (PathT.refl a) wS → X) (b : α) (e : PathT a b) :
    (⟨(jPoint F G wS wP b e).1, k ∘ (jPoint F G wS wP b e).2⟩ : Σ s : F b e, (G b e s → Y)) =
      jPoint F G wS (k ∘ wP) b e := by
  obtain ⟨⟨rfl⟩⟩ := e
  rfl

section Identity

variable {Γ Δ : Ctx.{u}} {A : Ty Γ}

/-- The identity type: the paths between the shapes, with no positions (Proposition 3.8 and
Remark 3.9). -/
def Ty.eq (u v : Tm Γ A) : Ty Γ := Ty.modal fun γ => PathT (u.S γ) (v.S γ)

/-- The identity type is stable under substitution, strictly. -/
theorem Ty.eq_sub (u v : Tm Γ A) (σ : Lens Δ Γ) :
    (Ty.eq u v).sub σ = Ty.eq (u.sub σ) (v.sub σ) := rfl

/-- The reflexive path of a term. -/
def Tm.refl (u : Tm Γ A) : Tm Γ (Ty.eq u u) := Tm.modalEquiv.symm fun γ => PathT.refl (u.S γ)

/-- **A path compares shapes only.** The type `u = v` has a term exactly when the shapes of `u` and
`v` are equal; the backward maps play no part. -/
theorem nonempty_tm_eq_iff {u v : Tm Γ A} : Nonempty (Tm Γ (Ty.eq u v)) ↔ ∀ γ, u.S γ = v.S γ :=
  ⟨fun ⟨p⟩ γ => (p.S γ).down.down, fun h => ⟨Tm.modalEquiv.symm fun γ => ⟨⟨h γ⟩⟩⟩⟩

/-- The family of the identity eliminator: a type over `Γ`, a point of `A` and a path from `u` to
that point. -/
abbrev JCtx (u : Tm Γ A) : Ctx.{u} := ext (ext Γ A) (Ty.eq (u.sub (wk A)) (var A))

/-- The substitution of a point and a path into the context of the eliminator. -/
def pathSub (u v : Tm Γ A) (p : Tm Γ (Ty.eq u v)) : Lens Γ (JCtx u) :=
  extend (inst v) p

/-- **The identity eliminator.** On shapes it is path induction in the base; on positions it is the
backward map of `w` after the transport of positions along the path. -/
def Tm.J (u : Tm Γ A) (D : Ty (JCtx u)) (w : Tm Γ (D.sub (pathSub u u (Tm.refl u)))) (v : Tm Γ A)
    (p : Tm Γ (Ty.eq u v)) : Tm Γ (D.sub (pathSub u v p)) :=
  Tm.ofSection fun γ =>
    jPoint (a := u.S γ) (F := fun b e => D.S ⟨⟨γ, b⟩, e⟩) (G := fun b e s => D.P ⟨⟨γ, b⟩, e⟩ s)
      (w.S γ) (w.P γ) (v.S γ) (p.S γ)

/-- The β law of the identity eliminator, strictly. -/
theorem Tm.J_refl (u : Tm Γ A) (D : Ty (JCtx u)) (w : Tm Γ (D.sub (pathSub u u (Tm.refl u)))) :
    Tm.J u D w u (Tm.refl u) = w := rfl

/-- The identity eliminator is stable under substitution. The backward map is compared by path
induction. -/
theorem Tm.J_sub (u : Tm Γ A) (D : Ty (JCtx u)) (w : Tm Γ (D.sub (pathSub u u (Tm.refl u))))
    (v : Tm Γ A) (p : Tm Γ (Ty.eq u v)) (σ : Lens Δ Γ) :
    (Tm.J u D w v p).sub σ =
      Tm.J (u.sub σ) (D.sub (lift (lift σ A) (Ty.eq (u.sub (wk A)) (var A)))) (w.sub σ) (v.sub σ)
        (p.sub σ) :=
  Tm.ext_section fun d =>
    jPoint_map (a := u.S (σ.toFunA d))
      (fun b e => D.S ⟨⟨σ.toFunA d, b⟩, e⟩) (fun b e s => D.P ⟨⟨σ.toFunA d, b⟩, e⟩ s)
      (σ.toFunB d) (w.S (σ.toFunA d)) (w.P (σ.toFunA d)) (v.S (σ.toFunA d)) (p.S (σ.toFunA d))

end Identity

/-! ## Coproducts -/

section Coproduct

variable {Γ Δ : Ctx.{u}} {A B : Ty Γ}

/-- The empty type (Proposition 3.13). -/
def Ty.empty (Γ : Ctx.{u}) : Ty Γ := Ty.modal fun _ => PEmpty

/-- The eliminator of the empty type. -/
def Tm.emptyElim (C : Ty Γ) (e : Tm Γ (Ty.empty Γ)) : Tm Γ C where
  S γ := (e.S γ).elim
  P γ := (e.S γ).elim

/-- The binary coproduct: the sum of the shapes, with the positions of the component
(Proposition 3.13). -/
def Ty.coprod (A B : Ty Γ) : Ty Γ where
  S γ := A.S γ ⊕ B.S γ
  P γ := Sum.elim (A.P γ) (B.P γ)

/-- The coproduct is stable under substitution, strictly. -/
theorem Ty.coprod_sub (A B : Ty Γ) (σ : Lens Δ Γ) :
    (Ty.coprod A B).sub σ = Ty.coprod (A.sub σ) (B.sub σ) := rfl

/-- The left injection, with the backward map of the term. -/
def Tm.inl (a : Tm Γ A) : Tm Γ (Ty.coprod A B) where
  S γ := Sum.inl (a.S γ)
  P := a.P

/-- The right injection, with the backward map of the term. -/
def Tm.inr (b : Tm Γ B) : Tm Γ (Ty.coprod A B) where
  S γ := Sum.inr (b.S γ)
  P := b.P

/-- The substitution over the left injection. -/
abbrev inlSub (A B : Ty Γ) : Lens (ext Γ A) (ext Γ (Ty.coprod A B)) :=
  extend (wk A) (Tm.inl (B := B.sub (wk A)) (var A))

/-- The substitution over the right injection. -/
abbrev inrSub (A B : Ty Γ) : Lens (ext Γ B) (ext Γ (Ty.coprod A B)) :=
  extend (wk B) (Tm.inr (A := A.sub (wk B)) (var B))

variable {C : Ty (ext Γ (Ty.coprod A B))}

/-- The case split at a shape of the coproduct: the shape and the backward map of the branch, whose
positions are those of the context or those of the scrutinee. -/
def casePoint (l : Tm (ext Γ A) (C.sub (inlSub A B))) (r : Tm (ext Γ B) (C.sub (inrSub A B)))
    (γ : Γ.A) : ∀ s : A.S γ ⊕ B.S γ,
      Σ x : C.S ⟨γ, s⟩, (C.P ⟨γ, s⟩ x → Γ.B γ ⊕ (Ty.coprod A B).P γ s)
  | .inl a => ⟨l.S ⟨γ, a⟩, l.P ⟨γ, a⟩⟩
  | .inr b => ⟨r.S ⟨γ, b⟩, r.P ⟨γ, b⟩⟩

/-- The eliminator of the coproduct. A position of the result goes back through the branch, and a
position of the scrutinee goes back through the scrutinee. -/
def Tm.case (l : Tm (ext Γ A) (C.sub (inlSub A B))) (r : Tm (ext Γ B) (C.sub (inrSub A B)))
    (c : Tm Γ (Ty.coprod A B)) : Tm Γ (C.sub (inst c)) where
  S γ := (casePoint l r γ (c.S γ)).1
  P γ x := (inst c).toFunB γ ((casePoint l r γ (c.S γ)).2 x)

/-- The β law at the left injection, strictly. -/
theorem Tm.case_inl (l : Tm (ext Γ A) (C.sub (inlSub A B))) (r : Tm (ext Γ B) (C.sub (inrSub A B)))
    (a : Tm Γ A) : Tm.case l r (Tm.inl a) = l.sub (inst a) := rfl

/-- The β law at the right injection, strictly. -/
theorem Tm.case_inr (l : Tm (ext Γ A) (C.sub (inlSub A B))) (r : Tm (ext Γ B) (C.sub (inrSub A B)))
    (b : Tm Γ B) : Tm.case l r (Tm.inr b) = r.sub (inst b) := rfl

/-- The case split at a shape of the restrictions of a term over the coproduct is that term. -/
theorem casePoint_eta (x : Tm (ext Γ (Ty.coprod A B)) C) (γ : Γ.A) (s : A.S γ ⊕ B.S γ) :
    casePoint (x.sub (inlSub A B)) (x.sub (inrSub A B)) γ s = ⟨x.S ⟨γ, s⟩, x.P ⟨γ, s⟩⟩ := by
  cases s with
  | inl a =>
    refine congrArg (Sigma.mk _) (funext fun y => ?_)
    change (inlSub A B).toFunB ⟨γ, a⟩ (x.P ⟨γ, Sum.inl a⟩ y) = x.P ⟨γ, Sum.inl a⟩ y
    generalize x.P ⟨γ, Sum.inl a⟩ y = z
    cases z <;> rfl
  | inr b =>
    refine congrArg (Sigma.mk _) (funext fun y => ?_)
    change (inrSub A B).toFunB ⟨γ, b⟩ (x.P ⟨γ, Sum.inr b⟩ y) = x.P ⟨γ, Sum.inr b⟩ y
    generalize x.P ⟨γ, Sum.inr b⟩ y = z
    cases z <;> rfl

/-- The η law of the coproduct: a term over the coproduct is the case split of its restrictions. -/
theorem Tm.case_eta (x : Tm (ext Γ (Ty.coprod A B)) C) (c : Tm Γ (Ty.coprod A B)) :
    Tm.case (x.sub (inlSub A B)) (x.sub (inrSub A B)) c = x.sub (inst c) :=
  Tm.ext_section fun γ =>
    congrArg (fun r : Σ y : C.S ⟨γ, c.S γ⟩,
        (C.P ⟨γ, c.S γ⟩ y → Γ.B γ ⊕ (Ty.coprod A B).P γ (c.S γ)) =>
      (⟨r.1, fun y => (inst c).toFunB γ (r.2 y)⟩ :
        Σ y : C.S ⟨γ, c.S γ⟩, (C.P ⟨γ, c.S γ⟩ y → Γ.B γ))) (casePoint_eta x γ (c.S γ))

/-- The case split at a shape, in a substituted context, is the case split in the original context
followed by the weakened substitution. -/
theorem casePoint_sub (l : Tm (ext Γ A) (C.sub (inlSub A B)))
    (r : Tm (ext Γ B) (C.sub (inrSub A B))) (σ : Lens Δ Γ) (d : Δ.A)
    (s : A.S (σ.toFunA d) ⊕ B.S (σ.toFunA d)) :
    casePoint (A := A.sub σ) (B := B.sub σ) (C := C.sub (lift σ (Ty.coprod A B)))
        (l.sub (lift σ A)) (r.sub (lift σ B)) d s =
      ⟨(casePoint l r (σ.toFunA d) s).1,
        fun y => (lift σ (Ty.coprod A B)).toFunB ⟨d, s⟩ ((casePoint l r (σ.toFunA d) s).2 y)⟩ := by
  cases s <;> rfl

/-- The eliminator of the coproduct is stable under substitution. The backward map is compared by
a case split on the sum of positions. -/
theorem Tm.case_sub (l : Tm (ext Γ A) (C.sub (inlSub A B)))
    (r : Tm (ext Γ B) (C.sub (inrSub A B))) (c : Tm Γ (Ty.coprod A B)) (σ : Lens Δ Γ) :
    (Tm.case l r c).sub σ =
      Tm.case (A := A.sub σ) (B := B.sub σ) (C := C.sub (lift σ (Ty.coprod A B)))
        (l.sub (lift σ A)) (r.sub (lift σ B)) (c.sub σ) := by
  refine Tm.ext_section fun d => ?_
  have h := casePoint_sub l r σ d (c.S (σ.toFunA d))
  have key : ∀ z : Γ.B (σ.toFunA d) ⊕ (Ty.coprod A B).P (σ.toFunA d) (c.S (σ.toFunA d)),
      σ.toFunB d ((inst c).toFunB (σ.toFunA d) z) =
        (inst (A := (Ty.coprod A B).sub σ) (c.sub σ)).toFunB d
          ((lift σ (Ty.coprod A B)).toFunB ⟨d, c.S (σ.toFunA d)⟩ z) := fun z => by
    cases z <;> rfl
  refine Eq.trans (congrArg (Sigma.mk _) (funext fun y => key _)) (Eq.symm ?_)
  exact congrArg (fun r => (⟨r.1, fun y => (inst (A := (Ty.coprod A B).sub σ) (c.sub σ)).toFunB d
    (r.2 y)⟩ : Σ y : C.S ⟨σ.toFunA d, c.S (σ.toFunA d)⟩,
      (C.P ⟨σ.toFunA d, c.S (σ.toFunA d)⟩ y → Δ.B d))) h

end Coproduct

end CatCrypt.Container.CwF
