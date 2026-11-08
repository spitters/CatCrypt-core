/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.RGraphCwF
public import CatCryptCore.Container.CwFPi
public import CatCryptCore.Container.DNRel

/-!
# The polynomial model over the reflexive-graph model

This module gives the polynomial construction of Moss and von Glehn (§6) with base model the
reflexive-graph category with families of `CatCryptCore.Container.RGraphCwF` (Atkey, Ghani and
Johann), in the layout of `CatCryptCore.Container.CwF`, which is the same construction over `Type`.

A context (`Ctx`) is a reflexive graph `Γ.A` of shapes with a type `Γ.B` of positions over it, both
in the base. A substitution (`Hom`) is a lens of the base: a morphism of reflexive graphs `f` on
shapes and a term `b` of the base that sends the positions of the target back to those of the
source; `b` preserves the relations of positions over every edge. A type (`Ty`) is a base type `S`
of shapes over `Γ.A` with a base type `P` of positions over the extension by `S`; a term (`Tm`) is a
base term of shapes with a backward base term on positions. Context extension (`ext`) takes the
base extension on shapes and the base sum (`Base.sum`) on positions.

Which laws are strict. As in `CatCryptCore.Container.CwF`, the category laws, the substitution laws
of types and terms, the projection laws of context extension, the stability of `Ty.sigma`, `Ty.pi`,
`Ty.eq` and `Ty.modal` and the β laws of `Ty.sigma` hold by `rfl`; the laws that compare two maps
out of a sum of positions or out of the empty type hold by a case split (`extend_wk_var`,
`extend_comp`, `toUnit_unique`, `Tm.mkPair_fst_snd`). The relations of base types are
propositions, so two base terms with the same values are equal (`Base.tm_ext`).

The identity type compares shapes only, and since a base term carries its edges as proofs, a path
between two terms is an equality of their shape terms of the base, edges included
(`nonempty_tm_eq_iff`). The base functor `Γ ↦ Γ.A` has the right adjoint `disc` (`discHomEquiv`),
and `Ty.modal` is the induced dependent right adjoint (`Tm.modalEquiv`).

Forgetting the edges is a strict morphism of categories with families into the polynomial model over
`Type` (`Ctx.forget`, `Hom.forget`, `Ty.forget`, `Tm.forget`). Over an edge `e` of the shapes of a
context, a type gives a signature relation between its containers at the two ends (`Ty.edgeRel`): a
relation of shapes and, over related shapes, a relation of positions, the Prop-valued form of a
`ContParam .map0 .map0 .map0 .map0` relation. A vertical lens between types gives a square of these
relations over each edge (`TyHom.square`). Over the walking edge (`walk`), every signature relation
arises this way (`Ty.ofSigRel`, `Ty.edgeRel_ofSigRel`), and every square of signature relations is a
vertical lens (`TyHom.ofSquare`).

The dependent product (`Ty.pi`) has as shapes the shapes of the product of the polynomial model over
`Type` (`CwF.PiShape`: a forward map and a partial backward map), related over an edge when related
arguments go to related results and related result positions go back to related optional argument
positions. Abstraction and application are those of the model over `Type`, which preserve the
relations; since forgetting is injective on terms (`Tm.forget_injective`), the β and η laws and
the naturality of abstraction and application follow from those over `Type`.

## Main definitions

* `Ctx`, `Hom`, `Ty`, `Tm`, `Ty.sub`, `Tm.sub` — contexts, lenses, types and terms;
* `unit`, `toUnit`, `ext`, `wk`, `var`, `extend`, `inst`, `lift` — the substitution calculus;
* `Ty.sigma`, `Tm.mkPair`, `Tm.fst`, `Tm.snd` — dependent sums;
* `Ty.pi`, `Tm.lam`, `Tm.app` — dependent products;
* `Ty.eq`, `Tm.refl` — identity types;
* `disc`, `discUnit`, `Ty.modal`, `Tm.toModal` — the reflective modality;
* `Ctx.forget`, `Hom.forget`, `Ty.forget`, `Tm.forget` — the morphism into the polynomial model
  over `Type`;
* `Ty.fibre`, `Ty.edgeRel`, `TyHom`, `walk`, `Ty.ofSigRel`, `TyHom.ofSquare` — the comparison
  with relations of containers.

## Main results

* `hom_id_comp`, `hom_comp_id`, `hom_comp_assoc`, `Ty.sub_id`, `Ty.sub_comp`, `Tm.sub_id`,
  `Tm.sub_comp` — the category with families laws;
* `wk_extend`, `var_sub_extend`, `extend_wk_var`, `extend_comp` — the comprehension laws;
* `Ty.sigma_sub`, `Tm.fst_mkPair`, `Tm.snd_mkPair`, `Tm.mkPair_fst_snd` — dependent sums;
* `Ty.pi_sub`, `Tm.app_lam`, `Tm.lam_app`, `Tm.lamEquiv`, `Tm.lam_sub`, `Tm.app_sub` — dependent
  products;
* `Ty.eq_sub`, `nonempty_tm_eq_iff` — paths compare shapes, edges included;
* `discHomEquiv`, `Tm.modalEquiv` — the reflection and the dependent right adjoint;
* `Ty.forget_sub`, `Tm.forget_sub`, `Ctx.forget_ext`, `Ty.forget_sigma`, `Ty.forget_eq` — the
  forgetful morphism is strict;
* `TyHom.square` — a vertical lens is a square of signature relations over every edge;
* `Ty.edgeRel_ofSigRel` — every signature relation is the edge relation of a type over the walking
  edge;
* `TyHom.ofSquare_fibre_src`, `TyHom.ofSquare_fibre_tgt` — every square of signature relations is
  a vertical lens over the walking edge.

## References

* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018, §6;
* R. Atkey, N. Ghani, P. Johann, *A relationally parametric model of dependent type theory*,
  POPL 2014;
* T. von Glehn, *Polynomials and models of type theory*, PhD thesis, Cambridge, 2015;
* E. Cavallo, T. Höfer, *Univalence without function extensionality*, arXiv:2605.00812, §3.

Search words: category with families, CwF, polynomial model, container model, reflexive graph,
relational parametricity, lens, context extension, dependent sum, identity type, modality,
signature relation, ContParam, logical relation.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container.PolyRGraph

open PFunctor

/-! ## Auxiliary types of the base -/

namespace Base

variable {Γ : RGraphCwF.Ctx.{u}}

/-- The binary sum of two types of the reflexive-graph model: the sum of the sets, related
componentwise. -/
def sum (A B : RGraphCwF.Ty Γ) : RGraphCwF.Ty Γ where
  V γ := A.V γ ⊕ B.V γ
  E e := Sum.LiftRel (A.E e) (B.E e)
  refl_iff γ x y := by
    cases x <;> cases y <;> simp [A.refl_iff, B.refl_iff]

/-- The empty type of the reflexive-graph model. -/
abbrev empty (Γ : RGraphCwF.Ctx.{u}) : RGraphCwF.Ty Γ := RGraphCwF.Ty.disc Γ PEmpty

/-- The paths between the values of two terms, every edge relating every pair of paths. -/
def path {A : RGraphCwF.Ty Γ} (a b : RGraphCwF.Tm Γ A) : RGraphCwF.Ty Γ where
  V γ := CwF.PathT (a.V γ) (b.V γ)
  E _ _ _ := True
  refl_iff _ p q := ⟨fun _ => Subsingleton.elim p q, fun _ => trivial⟩

/-- Two terms of the base with the same values are equal: edges of types are propositions. -/
theorem tm_ext {A : RGraphCwF.Ty Γ} {a b : RGraphCwF.Tm Γ A} (h : ∀ γ, a.V γ = b.V γ) : a = b := by
  cases a
  cases b
  obtain rfl := funext h
  rfl

/-- The edge of a term over a context extension, at an edge of the context and a relatedness
proof. -/
theorem tmE {A : RGraphCwF.Ty Γ} {C : RGraphCwF.Ty (RGraphCwF.ext Γ A)}
    (t : RGraphCwF.Tm (RGraphCwF.ext Γ A) C) {γ γ' : Γ.V} (e : Γ.E γ γ') {a : A.V γ} {a' : A.V γ'}
    (r : A.E e a a') : C.E ⟨e, r⟩ (t.V ⟨γ, a⟩) (t.V ⟨γ', a'⟩) :=
  t.E (γ := ⟨γ, a⟩) (γ' := ⟨γ', a'⟩) ⟨e, r⟩

/-- The copairing of two maps sends componentwise related arguments to related values. -/
theorem liftRel_elim {α β γ α' β' γ' : Type u} {r : α → α' → Prop} {s : β → β' → Prop}
    {t : γ → γ' → Prop} {f : α → γ} {g : β → γ} {f' : α' → γ'} {g' : β' → γ'}
    (hf : ∀ a a', r a a' → t (f a) (f' a')) (hg : ∀ b b', s b b' → t (g b) (g' b'))
    {x : α ⊕ β} {y : α' ⊕ β'} (h : Sum.LiftRel r s x y) :
    t (Sum.elim f g x) (Sum.elim f' g' y) := by
  cases h with
  | inl h => exact hf _ _ h
  | inr h => exact hg _ _ h

end Base

/-! ## Contexts and substitutions -/

/-- A context of the model: a reflexive graph of shapes and a type of positions over it. -/
structure Ctx : Type (u + 1) where
  /-- The reflexive graph of shapes. -/
  A : RGraphCwF.Ctx.{u}
  /-- The positions, a type over the shapes. -/
  B : RGraphCwF.Ty A

/-- A substitution: a morphism of the graphs of shapes and a backward term on positions. -/
structure Hom (Δ Γ : Ctx.{u}) : Type u where
  /-- The forward map on shapes. -/
  f : RGraphCwF.Hom Δ.A Γ.A
  /-- The backward map on positions, preserving their relations. -/
  b : RGraphCwF.Tm (RGraphCwF.ext Δ.A (Γ.B.sub f)) (Δ.B.sub (RGraphCwF.wk _))

section Category

variable {Γ Δ Θ Ξ : Ctx.{u}}

/-- Two substitutions with the same forward map are equal when their backward maps agree. -/
theorem Hom.ext_b {f : RGraphCwF.Hom Δ.A Γ.A}
    {b b' : RGraphCwF.Tm (RGraphCwF.ext Δ.A (Γ.B.sub f)) (Δ.B.sub (RGraphCwF.wk _))}
    (h : ∀ p, b.V p = b'.V p) : (Hom.mk f b : Hom Δ Γ) = Hom.mk f b' :=
  congrArg (Hom.mk f) (Base.tm_ext h)

/-- The identity substitution. -/
def Hom.id (Γ : Ctx.{u}) : Hom Γ Γ where
  f := RGraphCwF.Hom.id Γ.A
  b := ⟨fun p => p.2, fun e => e.2⟩

/-- Composition of substitutions, `σ` after `τ`. -/
def Hom.comp (σ : Hom Δ Γ) (τ : Hom Θ Δ) : Hom Θ Γ where
  f := σ.f.comp τ.f
  b := ⟨fun p => τ.b.V ⟨p.1, σ.b.V ⟨τ.f.map p.1, p.2⟩⟩,
    fun e => Base.tmE τ.b e.1 (Base.tmE σ.b (τ.f.rel e.1) e.2)⟩

/-- The identity is a left unit, strictly. -/
theorem hom_id_comp (σ : Hom Δ Γ) : (Hom.id Γ).comp σ = σ := rfl

/-- The identity is a right unit, strictly. -/
theorem hom_comp_id (σ : Hom Δ Γ) : σ.comp (Hom.id Δ) = σ := rfl

/-- Composition is associative, strictly. -/
theorem hom_comp_assoc (σ : Hom Δ Γ) (τ : Hom Θ Δ) (ρ : Hom Ξ Θ) :
    (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) := rfl

end Category

/-! ## Types and terms -/

/-- A type over `Γ`: a base type of shapes, and a base type of positions over the shapes. -/
structure Ty (Γ : Ctx.{u}) : Type (u + 1) where
  /-- The shapes. -/
  S : RGraphCwF.Ty Γ.A
  /-- The positions over a shape. -/
  P : RGraphCwF.Ty (RGraphCwF.ext Γ.A S)

/-- A term: a base term of shapes and a backward base term from its positions to those of the
context. -/
structure Tm (Γ : Ctx.{u}) (A : Ty Γ) : Type u where
  /-- The shapes of the term. -/
  S : RGraphCwF.Tm Γ.A A.S
  /-- The backward map on positions. -/
  P : RGraphCwF.Tm (RGraphCwF.ext Γ.A (A.P.sub (RGraphCwF.inst S))) (Γ.B.sub (RGraphCwF.wk _))

section Basic

variable {Γ Δ Θ : Ctx.{u}}

/-- Substitution in a type. -/
def Ty.sub (A : Ty Γ) (σ : Hom Δ Γ) : Ty Δ where
  S := A.S.sub σ.f
  P := A.P.sub (RGraphCwF.lift σ.f A.S)

/-- Substitution in a term: shapes reindexed, positions sent back through the term and then
through the substitution. -/
def Tm.sub {A : Ty Γ} (a : Tm Γ A) (σ : Hom Δ Γ) : Tm Δ (A.sub σ) where
  S := a.S.sub σ.f
  P := ⟨fun p => σ.b.V ⟨p.1, a.P.V ⟨σ.f.map p.1, p.2⟩⟩,
    fun e => Base.tmE σ.b e.1 (Base.tmE a.P (σ.f.rel e.1) e.2)⟩

/-- Types are stable under the identity substitution, strictly. -/
theorem Ty.sub_id (A : Ty Γ) : A.sub (Hom.id Γ) = A := rfl

/-- Types are stable under composition, strictly. -/
theorem Ty.sub_comp (A : Ty Γ) (τ : Hom Δ Γ) (σ : Hom Θ Δ) :
    A.sub (τ.comp σ) = (A.sub τ).sub σ := rfl

/-- Terms are stable under the identity substitution, strictly. -/
theorem Tm.sub_id {A : Ty Γ} (a : Tm Γ A) : (a.sub (Hom.id Γ) : Tm Γ A) = a := rfl

/-- Terms are stable under composition, strictly. -/
theorem Tm.sub_comp {A : Ty Γ} (a : Tm Γ A) (τ : Hom Δ Γ) (σ : Hom Θ Δ) :
    (a.sub (τ.comp σ) : Tm Θ ((A.sub τ).sub σ)) = (a.sub τ).sub σ := rfl

/-- Two terms with the same shapes are equal when their backward maps agree. -/
theorem Tm.ext_P {A : Ty Γ} {S : RGraphCwF.Tm Γ.A A.S}
    {P P' : RGraphCwF.Tm (RGraphCwF.ext Γ.A (A.P.sub (RGraphCwF.inst S)))
      (Γ.B.sub (RGraphCwF.wk _))}
    (h : ∀ p, P.V p = P'.V p) : (Tm.mk S P : Tm Γ A) = Tm.mk S P' :=
  congrArg (Tm.mk S) (Base.tm_ext h)

end Basic

/-! ## The substitution calculus -/

/-- The empty context: one shape and no positions. -/
def unit : Ctx.{u} := ⟨RGraphCwF.unit, Base.empty _⟩

/-- The extension of a context by a type: the base extension on shapes, the base sum of the
positions of the context and of the type. -/
def ext (Γ : Ctx.{u}) (A : Ty Γ) : Ctx.{u} :=
  ⟨RGraphCwF.ext Γ.A A.S, Base.sum (Γ.B.sub (RGraphCwF.wk A.S)) A.P⟩

section Calculus

variable {Γ Δ Θ : Ctx.{u}} {A : Ty Γ}

/-- The unique substitution into the empty context. -/
def toUnit (Γ : Ctx.{u}) : Hom Γ unit where
  f := RGraphCwF.toUnit Γ.A
  b := ⟨fun p => PEmpty.elim p.2, fun {p} _ => PEmpty.elim p.2⟩

/-- The empty context is terminal. -/
theorem toUnit_unique (σ : Hom Γ unit) : σ = toUnit Γ :=
  Hom.ext_b fun p => PEmpty.elim p.2

/-- The projection from a context extension. -/
def wk (A : Ty Γ) : Hom (ext Γ A) Γ where
  f := RGraphCwF.wk A.S
  b := ⟨fun p => Sum.inl p.2, fun e => Sum.LiftRel.inl e.2⟩

/-- The variable of a context extension. -/
def var (A : Ty Γ) : Tm (ext Γ A) (A.sub (wk A)) where
  S := RGraphCwF.var A.S
  P := ⟨fun p => Sum.inr p.2, fun e => Sum.LiftRel.inr e.2⟩

/-- The substitution into a context extension: on shapes the base extension, on positions the
copairing. -/
def extend (σ : Hom Δ Γ) (a : Tm Δ (A.sub σ)) : Hom Δ (ext Γ A) where
  f := RGraphCwF.extend σ.f a.S
  b := ⟨fun p => Sum.elim (fun c => σ.b.V ⟨p.1, c⟩) (fun x => a.P.V ⟨p.1, x⟩) p.2,
    fun e => Base.liftRel_elim (fun _ _ r => Base.tmE σ.b e.1 r) (fun _ _ r => Base.tmE a.P e.1 r)
      e.2⟩

/-- The substitution of a term for the last variable. -/
abbrev inst (a : Tm Γ A) : Hom Γ (ext Γ A) := extend (Hom.id Γ) a

/-- The weakening of a substitution under a binder. -/
abbrev lift (σ : Hom Δ Γ) (A : Ty Γ) : Hom (ext Δ (A.sub σ)) (ext Γ A) :=
  extend (σ.comp (wk (A.sub σ))) (var (A.sub σ))

/-- The projection after an extension is the original substitution, strictly. -/
theorem wk_extend (σ : Hom Δ Γ) (a : Tm Δ (A.sub σ)) : (wk A).comp (extend σ a) = σ := rfl

/-- The variable under an extension is the original term, strictly. -/
theorem var_sub_extend (σ : Hom Δ Γ) (a : Tm Δ (A.sub σ)) :
    ((var A).sub (extend σ a) : Tm Δ (A.sub σ)) = a := rfl

/-- The extension of the projection by the variable is the identity: the η law of the sum of
positions. -/
theorem extend_wk_var (A : Ty Γ) : extend (wk A) (var A) = Hom.id (ext Γ A) :=
  by refine Hom.ext_b fun p => ?_; obtain ⟨x, y | y⟩ := p <;> rfl

/-- Extension is natural in the domain: the η law of the sum of positions. -/
theorem extend_comp (σ : Hom Δ Γ) (a : Tm Δ (A.sub σ)) (τ : Hom Θ Δ) :
    (extend σ a).comp τ = extend (σ.comp τ) (a.sub τ) := by
  refine Hom.ext_b fun p => ?_
  obtain ⟨x, y | y⟩ := p <;> rfl

end Calculus

/-! ## Dependent sums -/

section Sigma

variable {Γ Δ : Ctx.{u}} {A : Ty Γ} {B : Ty (ext Γ A)}

/-- The base morphism from the extension by a base sum to the extension by its first component. -/
def sigmaFst {Γ : RGraphCwF.Ctx.{u}} (A : RGraphCwF.Ty Γ) (B : RGraphCwF.Ty (RGraphCwF.ext Γ A)) :
    RGraphCwF.Hom (RGraphCwF.ext Γ (RGraphCwF.Ty.sigma A B)) (RGraphCwF.ext Γ A) where
  map p := ⟨p.1, p.2.1⟩
  rel e := ⟨e.1, e.2.fst⟩
  rel_refl _ := rfl

/-- The base morphism from the extension by a base sum to the extension by both components. -/
def sigmaSnd {Γ : RGraphCwF.Ctx.{u}} (A : RGraphCwF.Ty Γ) (B : RGraphCwF.Ty (RGraphCwF.ext Γ A)) :
    RGraphCwF.Hom (RGraphCwF.ext Γ (RGraphCwF.Ty.sigma A B))
      (RGraphCwF.ext (RGraphCwF.ext Γ A) B) where
  map p := ⟨⟨p.1, p.2.1⟩, p.2.2⟩
  rel e := ⟨⟨e.1, e.2.fst⟩, e.2.snd⟩
  rel_refl _ := rfl

/-- The dependent sum: the base sum of shapes, and a position of either component. -/
def Ty.sigma (A : Ty Γ) (B : Ty (ext Γ A)) : Ty Γ where
  S := RGraphCwF.Ty.sigma A.S B.S
  P := Base.sum (A.P.sub (sigmaFst A.S B.S)) (B.P.sub (sigmaSnd A.S B.S))

/-- The dependent sum is stable under substitution, strictly. -/
theorem Ty.sigma_sub (A : Ty Γ) (B : Ty (ext Γ A)) (σ : Hom Δ Γ) :
    (Ty.sigma A B).sub σ = Ty.sigma (A.sub σ) (B.sub (lift σ A)) := rfl

/-- The pairing of terms. -/
def Tm.mkPair (a : Tm Γ A) (b : Tm Γ (B.sub (inst a))) : Tm Γ (Ty.sigma A B) where
  S := RGraphCwF.Tm.mkPair a.S b.S
  P := ⟨fun p => Sum.elim (fun x => a.P.V ⟨p.1, x⟩) (fun y => b.P.V ⟨p.1, y⟩) p.2,
    fun e => Base.liftRel_elim (fun _ _ r => Base.tmE a.P e.1 r) (fun _ _ r => Base.tmE b.P e.1 r)
      e.2⟩

/-- The first projection. -/
def Tm.fst (t : Tm Γ (Ty.sigma A B)) : Tm Γ A where
  S := RGraphCwF.Tm.fst t.S
  P := ⟨fun p => t.P.V ⟨p.1, Sum.inl p.2⟩, fun e => Base.tmE t.P e.1 (Sum.LiftRel.inl e.2)⟩

/-- The second projection. -/
def Tm.snd (t : Tm Γ (Ty.sigma A B)) : Tm Γ (B.sub (inst (Tm.fst t))) where
  S := RGraphCwF.Tm.snd t.S
  P := ⟨fun p => t.P.V ⟨p.1, Sum.inr p.2⟩, fun e => Base.tmE t.P e.1 (Sum.LiftRel.inr e.2)⟩

/-- The first projection of a pair, strictly. -/
theorem Tm.fst_mkPair (a : Tm Γ A) (b : Tm Γ (B.sub (inst a))) : Tm.fst (Tm.mkPair a b) = a := rfl

/-- The second projection of a pair, strictly. -/
theorem Tm.snd_mkPair (a : Tm Γ A) (b : Tm Γ (B.sub (inst a))) :
    (Tm.snd (Tm.mkPair a b) : Tm Γ (B.sub (inst a))) = b := rfl

/-- A term of a dependent sum is the pair of its projections: the η law of the sum of positions. -/
theorem Tm.mkPair_fst_snd (t : Tm Γ (Ty.sigma A B)) : Tm.mkPair (Tm.fst t) (Tm.snd t) = t :=
  by refine Tm.ext_P fun p => ?_; obtain ⟨x, y | y⟩ := p <;> rfl

end Sigma

/-! ## The reflective modality -/

/-- The context with shapes `X` and no positions. -/
def disc (X : RGraphCwF.Ctx.{u}) : Ctx.{u} := ⟨X, Base.empty X⟩

section Modal

variable {Γ Δ : Ctx.{u}} {X : RGraphCwF.Ctx.{u}}

/-- The unit of the reflection: the identity on shapes. -/
def discUnit (Γ : Ctx.{u}) : Hom Γ (disc Γ.A) where
  f := RGraphCwF.Hom.id Γ.A
  b := ⟨fun p => PEmpty.elim p.2, fun {p} _ => PEmpty.elim p.2⟩

/-- **The reflection.** A substitution into a context without positions is a morphism of the
graphs of shapes. -/
def discHomEquiv : Hom Δ (disc X) ≃ RGraphCwF.Hom Δ.A X where
  toFun σ := σ.f
  invFun f := ⟨f, ⟨fun p => PEmpty.elim p.2, fun {p} _ => PEmpty.elim p.2⟩⟩
  left_inv _ := Hom.ext_b fun p => PEmpty.elim p.2
  right_inv _ := rfl

/-- The type with shapes `F` and no positions. -/
def Ty.modal (F : RGraphCwF.Ty Γ.A) : Ty Γ := ⟨F, Base.empty _⟩

/-- The modal type is stable under substitution, strictly. -/
theorem Ty.modal_sub (F : RGraphCwF.Ty Γ.A) (σ : Hom Δ Γ) :
    (Ty.modal F).sub σ = Ty.modal (F.sub σ.f) := rfl

/-- **The dependent right adjoint.** A term of a modal type is a base term of its shapes. -/
def Tm.modalEquiv {F : RGraphCwF.Ty Γ.A} : Tm Γ (Ty.modal F) ≃ RGraphCwF.Tm Γ.A F where
  toFun a := a.S
  invFun s := ⟨s, ⟨fun p => PEmpty.elim p.2, fun {p} _ => PEmpty.elim p.2⟩⟩
  left_inv _ := Tm.ext_P fun p => PEmpty.elim p.2
  right_inv _ := rfl

/-- The unit of the modality at a type: a term keeps its shapes and forgets its backward map. -/
def Tm.toModal {A : Ty Γ} (a : Tm Γ A) : Tm Γ (Ty.modal A.S) :=
  Tm.modalEquiv.symm a.S

end Modal

/-! ## Identity types -/

section Identity

variable {Γ Δ : Ctx.{u}} {A : Ty Γ}

/-- The identity type: the paths between the shapes, with no positions. -/
def Ty.eq (u v : Tm Γ A) : Ty Γ := Ty.modal (Base.path u.S v.S)

/-- The identity type is stable under substitution, strictly. -/
theorem Ty.eq_sub (u v : Tm Γ A) (σ : Hom Δ Γ) :
    (Ty.eq u v).sub σ = Ty.eq (u.sub σ) (v.sub σ) := rfl

/-- The reflexive path of a term. -/
def Tm.refl (u : Tm Γ A) : Tm Γ (Ty.eq u u) :=
  Tm.modalEquiv.symm ⟨fun γ => CwF.PathT.refl (u.S.V γ), fun _ => trivial⟩

/-- **A path compares shapes only, edges included.** The type `u = v` has a term exactly when the
shape terms of `u` and `v` are equal as base terms; the backward maps play no part. -/
theorem nonempty_tm_eq_iff {u v : Tm Γ A} : Nonempty (Tm Γ (Ty.eq u v)) ↔ u.S = v.S :=
  ⟨fun ⟨p⟩ => Base.tm_ext fun γ => (p.S.V γ).down.down,
    fun h => ⟨Tm.modalEquiv.symm ⟨fun γ => ⟨⟨congrArg (fun t => t.V γ) h⟩⟩, fun _ => trivial⟩⟩⟩

end Identity

/-! ## The forgetful morphism into the polynomial model over `Type` -/

section Forget

variable {Γ Δ Θ : Ctx.{u}} {A : Ty Γ}

/-- The container of a context: its vertices of shapes and their positions. -/
def Ctx.forget (Γ : Ctx.{u}) : CwF.Ctx.{u} := ⟨Γ.A.V, Γ.B.V⟩

/-- The lens of a substitution. -/
def Hom.forget (σ : Hom Δ Γ) : Lens Δ.forget Γ.forget :=
  ⟨σ.f.map, fun δ c => σ.b.V ⟨δ, c⟩⟩

/-- The type of the polynomial model over `Type` underlying a type. -/
def Ty.forget (A : Ty Γ) : CwF.Ty Γ.forget := ⟨A.S.V, fun γ s => A.P.V ⟨γ, s⟩⟩

/-- The term of the polynomial model over `Type` underlying a term. -/
def Tm.forget (a : Tm Γ A) : CwF.Tm Γ.forget A.forget := ⟨a.S.V, fun γ x => a.P.V ⟨γ, x⟩⟩

/-- Forgetting preserves identities, strictly. -/
theorem Hom.forget_id (Γ : Ctx.{u}) : (Hom.id Γ).forget = Lens.id Γ.forget := rfl

/-- Forgetting preserves composition, strictly. -/
theorem Hom.forget_comp (σ : Hom Δ Γ) (τ : Hom Θ Δ) :
    (σ.comp τ).forget = Lens.comp σ.forget τ.forget := rfl

/-- Forgetting commutes with substitution in types, strictly. -/
theorem Ty.forget_sub (A : Ty Γ) (σ : Hom Δ Γ) : (A.sub σ).forget = A.forget.sub σ.forget := rfl

/-- Forgetting commutes with substitution in terms, strictly. -/
theorem Tm.forget_sub (a : Tm Γ A) (σ : Hom Δ Γ) : (a.sub σ).forget = a.forget.sub σ.forget :=
  rfl

/-- Forgetting preserves the empty context, strictly. -/
theorem Ctx.forget_unit : (unit : Ctx.{u}).forget = CwF.unit := rfl

/-- Forgetting preserves context extension, strictly. -/
theorem Ctx.forget_ext (A : Ty Γ) : (ext Γ A).forget = CwF.ext Γ.forget A.forget := rfl

/-- Forgetting preserves the projection, strictly. -/
theorem Hom.forget_wk (A : Ty Γ) : (wk A).forget = CwF.wk A.forget := rfl

/-- Forgetting preserves the variable, strictly. -/
theorem Tm.forget_var (A : Ty Γ) : (var A).forget = CwF.var A.forget := rfl

/-- Forgetting preserves the extension of a substitution, strictly. -/
theorem Hom.forget_extend (σ : Hom Δ Γ) (a : Tm Δ (A.sub σ)) :
    (extend σ a).forget = CwF.extend (A := A.forget) σ.forget a.forget := rfl

/-- Forgetting preserves dependent sums, strictly. -/
theorem Ty.forget_sigma (A : Ty Γ) (B : Ty (ext Γ A)) :
    (Ty.sigma A B).forget = CwF.Ty.sigma A.forget B.forget := rfl

/-- Forgetting preserves identity types, strictly. -/
theorem Ty.forget_eq (u v : Tm Γ A) : (Ty.eq u v).forget = CwF.Ty.eq u.forget v.forget := rfl

/-- Forgetting is injective on terms: the edges of a term are proofs. -/
theorem Tm.forget_injective {a b : Tm Γ A} (h : a.forget = b.forget) : a = b := by
  obtain ⟨⟨SV, SE⟩, ⟨PV, PE⟩⟩ := a
  obtain ⟨⟨SV', SE'⟩, ⟨PV', PE'⟩⟩ := b
  obtain rfl : SV = SV' := congrArg CwF.Tm.S h
  have hP γ := eq_of_heq (Sigma.mk.inj (congrFun (congrArg CwF.Tm.toSection h) γ)).2
  obtain rfl : PV = PV' := funext fun p => congrFun (hP p.1) p.2
  rfl

end Forget

/-! ## Dependent products -/

section PiAux

/-- A relation on options that is equality is equality on options. -/
theorem optionRel_iff_eq {α : Type u} {R : α → α → Prop} (h : ∀ a b, R a b ↔ a = b)
    (x y : Option α) : Option.Rel R x y ↔ x = y := by
  constructor
  · intro hr
    cases hr with
    | some hr => exact congrArg some ((h _ _).mp hr)
    | none => rfl
  · rintro rfl
    cases x with
    | none => exact .none
    | some a => exact .some ((h a a).mpr rfl)

/-- Componentwise related sums have related right parts. -/
theorem liftRel_getRight {α β α' β' : Type u} {r : α → α' → Prop} {s : β → β' → Prop}
    {x : α ⊕ β} {y : α' ⊕ β'} (h : Sum.LiftRel r s x y) :
    Option.Rel s x.getRight? y.getRight? := by
  cases h with
  | inl _ => exact .none
  | inr h => exact .some h

/-- Componentwise related sums that are both left have related left parts. -/
theorem liftRel_getLeft {α β α' β' : Type u} {r : α → α' → Prop} {s : β → β' → Prop}
    {x : α ⊕ β} {y : α' ⊕ β'} (h : Sum.LiftRel r s x y) (hx : x.isLeft) (hy : y.isLeft) :
    r (x.getLeft hx) (y.getLeft hy) := by
  cases h with
  | inl h => exact h
  | inr _ => simp at hx

/-- Application at shapes whose partial backward maps are related gives related sums. -/
theorem appPoint_liftRel {I I' : Type u} {AP BS : I → Type u} {BP : ∀ i, BS i → Type u}
    {AP' BS' : I' → Type u} {BP' : ∀ i, BS' i → Type u} {Z Z' : Type u}
    {T : Z → Z' → Prop} (s : CwF.PiShape AP BS BP) (s' : CwF.PiShape AP' BS' BP')
    (K : s.Pos → Z) (K' : s'.Pos → Z') {i : I} {i' : I'} {R : AP i → AP' i' → Prop}
    {b : BP i (s.fwd i)} {b' : BP' i' (s'.fwd i')}
    (hb : Option.Rel R (s.back i b) (s'.back i' b'))
    (hK : ∀ h h', T (K ⟨⟨i, b⟩, h⟩) (K' ⟨⟨i', b'⟩, h'⟩)) :
    Sum.LiftRel T R (CwF.appPoint s K i b) (CwF.appPoint s' K' i' b') := by
  rcases h1 : s.back i b with _ | d <;> rcases h2 : s'.back i' b' with _ | d' <;>
    rw [h1, h2] at hb
  · rw [CwF.appPoint_of_none _ _ h1, CwF.appPoint_of_none _ _ h2]
    exact .inl (hK h1 h2)
  · cases hb
  · cases hb
  · rw [CwF.appPoint_of_some _ _ h1, CwF.appPoint_of_some _ _ h2]
    cases hb with
    | some hr => exact .inr hr

end PiAux

section Pi

variable {Γ Δ : Ctx.{u}} {A : Ty Γ} {B : Ty (ext Γ A)}

/-- The shapes of the function type at a vertex: a forward map on shapes and a partial backward map
on positions, as in the polynomial model over `Type`. -/
abbrev PiS (A : Ty Γ) (B : Ty (ext Γ A)) (γ : Γ.A.V) : Type u :=
  CwF.PiShape (fun a : A.S.V γ => A.P.V ⟨γ, a⟩) (fun a => B.S.V ⟨γ, a⟩)
    (fun a y => B.P.V ⟨⟨γ, a⟩, y⟩)

/-- The relation of shapes of the function type over an edge: related arguments go to related
results, and related positions of the results go back to related optional positions of the
arguments. -/
def piShapeRel (A : Ty Γ) (B : Ty (ext Γ A)) {γ γ' : Γ.A.V} (e : Γ.A.E γ γ') (s : PiS A B γ)
    (s' : PiS A B γ') : Prop :=
  (∀ a a' (r : A.S.E e a a'), B.S.E ⟨e, r⟩ (s.fwd a) (s'.fwd a')) ∧
    ∀ a a' (r : A.S.E e a a') (q : B.S.E ⟨e, r⟩ (s.fwd a) (s'.fwd a'))
      (b : B.P.V ⟨⟨γ, a⟩, s.fwd a⟩) (b' : B.P.V ⟨⟨γ', a'⟩, s'.fwd a'⟩),
      B.P.E ⟨⟨e, r⟩, q⟩ b b' → Option.Rel (A.P.E ⟨e, r⟩) (s.back a b) (s'.back a' b')

/-- Identity extension for the shapes of the function type. -/
theorem piShapeRel_refl_iff (A : Ty Γ) (B : Ty (ext Γ A)) (γ : Γ.A.V) (s s' : PiS A B γ) :
    piShapeRel A B (Γ.A.refl γ) s s' ↔ s = s' := by
  constructor
  · rintro ⟨hf, hb⟩
    obtain ⟨f, k⟩ := s
    obtain ⟨f', k'⟩ := s'
    obtain rfl : f = f' := funext fun a =>
      (B.S.refl_iff ⟨γ, a⟩ _ _).mp (hf a a ((A.S.refl_iff γ a a).mpr rfl))
    refine congrArg (CwF.PiShape.mk f) (funext fun a => funext fun b => ?_)
    exact (optionRel_iff_eq (A.P.refl_iff ⟨γ, a⟩) _ _).mp
      (hb a a ((A.S.refl_iff γ a a).mpr rfl) ((B.S.refl_iff ⟨γ, a⟩ _ _).mpr rfl) b b
        ((B.P.refl_iff ⟨⟨γ, a⟩, f a⟩ b b).mpr rfl))
  · rintro rfl
    refine ⟨fun a a' r => ?_, fun a a' r _ b b' rb => ?_⟩
    · obtain rfl := (A.S.refl_iff γ a a').mp r
      exact (B.S.refl_iff ⟨γ, a⟩ _ _).mpr rfl
    · obtain rfl := (A.S.refl_iff γ a a').mp r
      obtain rfl := (B.P.refl_iff ⟨⟨γ, a⟩, s.fwd a⟩ b b').mp rb
      exact (optionRel_iff_eq (A.P.refl_iff ⟨γ, a⟩) _ _).mpr rfl

/-- The dependent product: shapes are forward maps with partial backward maps, related as in
`piShapeRel`; positions are the argument and result positions on which the backward map is
`none`, related over related arguments. -/
def Ty.pi (A : Ty Γ) (B : Ty (ext Γ A)) : Ty Γ where
  S := ⟨PiS A B, piShapeRel A B, piShapeRel_refl_iff A B⟩
  P := ⟨fun p => p.2.Pos,
    fun e x x' => ∃ r : A.S.E e.1 x.1.1 x'.1.1, B.P.E ⟨⟨e.1, r⟩, e.2.1 _ _ r⟩ x.1.2 x'.1.2,
    fun p x x' => by
      obtain ⟨⟨a, b⟩, h⟩ := x
      obtain ⟨⟨a', b'⟩, h'⟩ := x'
      constructor
      · rintro ⟨r, rb⟩
        obtain rfl := (A.S.refl_iff p.1 a a').mp r
        obtain rfl := (B.P.refl_iff ⟨⟨p.1, a⟩, p.2.fwd a⟩ b b').mp rb
        rfl
      · rintro ⟨⟩
        exact ⟨(A.S.refl_iff p.1 a a).mpr rfl, (B.P.refl_iff _ b b).mpr rfl⟩⟩

/-- The dependent product is stable under substitution, strictly. -/
theorem Ty.pi_sub (A : Ty Γ) (B : Ty (ext Γ A)) (σ : Hom Δ Γ) :
    (Ty.pi A B).sub σ = Ty.pi (A.sub σ) (B.sub (lift σ A)) := rfl

/-- Forgetting preserves dependent products, strictly. -/
theorem Ty.forget_pi (A : Ty Γ) (B : Ty (ext Γ A)) :
    (Ty.pi A B).forget = CwF.Ty.pi A.forget B.forget := rfl

/-- Abstraction: the abstraction of the polynomial model over `Type`, which preserves edges. -/
def Tm.lam (t : Tm (ext Γ A) B) : Tm Γ (Ty.pi A B) where
  S := ⟨fun γ => (CwF.Tm.lam (Γ := Γ.forget) (A := A.forget) t.forget).S γ,
    fun {γ γ'} e => ⟨fun _ _ r => Base.tmE t.S e r, fun a a' r _ b b' rb =>
      liftRel_getRight (Base.tmE t.P (γ := ⟨γ, a⟩) (γ' := ⟨γ', a'⟩) ⟨e, r⟩ rb)⟩⟩
  P := ⟨fun p => (CwF.Tm.lam (Γ := Γ.forget) (A := A.forget) t.forget).P p.1 p.2,
    fun {p q} e => by
      obtain ⟨r, rb⟩ := e.2
      exact liftRel_getLeft
        (Base.tmE t.P (γ := ⟨p.1, p.2.1.1⟩) (γ' := ⟨q.1, q.2.1.1⟩) ⟨e.1, r⟩ rb) _ _⟩

/-- Application to the last variable: the application of the polynomial model over `Type`, which
preserves edges. -/
def Tm.app (f : Tm Γ (Ty.pi A B)) : Tm (ext Γ A) B where
  S := ⟨fun p => (CwF.Tm.app (Γ := Γ.forget) (A := A.forget) (B := B.forget) f.forget).S p,
    fun {p q} e => (f.S.E e.1).1 p.2 q.2 e.2⟩
  P := ⟨fun p => (CwF.Tm.app (Γ := Γ.forget) (A := A.forget) (B := B.forget) f.forget).P p.1 p.2,
    fun {p q} e => by
      obtain ⟨⟨e0, r⟩, rb⟩ := e
      exact appPoint_liftRel (T := Γ.B.E e0) (f.S.V p.1.1) (f.S.V q.1.1) (fun x => f.P.V ⟨p.1.1, x⟩)
        (fun x => f.P.V ⟨q.1.1, x⟩) ((f.S.E e0).2 _ _ r _ _ _ rb) fun h h' =>
          Base.tmE f.P e0 (a := ⟨⟨p.1.2, p.2⟩, h⟩) (a' := ⟨⟨q.1.2, q.2⟩, h'⟩) ⟨r, rb⟩⟩

/-- Forgetting preserves abstraction, strictly. -/
theorem Tm.forget_lam (t : Tm (ext Γ A) B) :
    (Tm.lam t).forget = CwF.Tm.lam (Γ := Γ.forget) (A := A.forget) t.forget := rfl

/-- Forgetting preserves application, strictly. -/
theorem Tm.forget_app (f : Tm Γ (Ty.pi A B)) :
    (Tm.app f).forget = CwF.Tm.app (Γ := Γ.forget) (A := A.forget) (B := B.forget) f.forget := rfl

/-- The β law of Π. -/
theorem Tm.app_lam (t : Tm (ext Γ A) B) : Tm.app (Tm.lam t) = t :=
  Tm.forget_injective (CwF.Tm.app_lam (Γ := Γ.forget) (A := A.forget) t.forget)

/-- The η law of Π. -/
theorem Tm.lam_app (f : Tm Γ (Ty.pi A B)) : Tm.lam (Tm.app f) = f :=
  Tm.forget_injective (CwF.Tm.lam_app (Γ := Γ.forget) (A := A.forget) (B := B.forget) f.forget)

/-- **The bijection of abstraction and application.** -/
def Tm.lamEquiv : Tm (ext Γ A) B ≃ Tm Γ (Ty.pi A B) where
  toFun := Tm.lam
  invFun := Tm.app
  left_inv := Tm.app_lam
  right_inv := Tm.lam_app

/-- Abstraction is natural in the context. -/
theorem Tm.lam_sub (t : Tm (ext Γ A) B) (σ : Hom Δ Γ) :
    (Tm.lam t).sub σ = Tm.lam (A := A.sub σ) (B := B.sub (lift σ A)) (t.sub (lift σ A)) :=
  Tm.forget_injective (CwF.Tm.lam_sub (Γ := Γ.forget) (A := A.forget) t.forget σ.forget)

/-- Application is natural in the context. -/
theorem Tm.app_sub (f : Tm Γ (Ty.pi A B)) (σ : Hom Δ Γ) :
    (Tm.app f).sub (lift σ A) = Tm.app (A := A.sub σ) (B := B.sub (lift σ A)) (f.sub σ) :=
  Tm.forget_injective
    (CwF.Tm.app_sub (Γ := Γ.forget) (A := A.forget) (B := B.forget) f.forget σ.forget)

end Pi

/-! ## Relations of containers over edges -/

section Comparison

variable {Γ : Ctx.{u}}

/-- The container of a type at a vertex of the shapes of the context. -/
def Ty.fibre (T : Ty Γ) (γ : Γ.A.V) : PFunctor.{u, u} := ⟨T.S.V γ, fun s => T.P.V ⟨γ, s⟩⟩

/-- The signature relation of a type over an edge: shapes related over the edge, and positions
related over every proof that their shapes are related. -/
def Ty.edgeRel (T : Ty Γ) {γ γ' : Γ.A.V} (e : Γ.A.E γ γ') : SigRel (T.fibre γ) (T.fibre γ') where
  pos := T.S.E e
  dir _ _ x x' := ∀ r, T.P.E ⟨e, r⟩ x x'

/-- Over a reflexive edge the signature relation of a type is the identity. -/
theorem Ty.edgeRel_refl_isId (T : Ty Γ) (γ : Γ.A.V) : (T.edgeRel (Γ.A.refl γ)).IsId where
  pos_iff s s' := T.S.refl_iff γ s s'
  dir_iff s x x' := by
    refine ⟨fun h => ?_, fun h r => ?_⟩
    · exact (T.P.refl_iff ⟨γ, s⟩ x x').mp (h _)
    · exact (T.P.refl_iff ⟨γ, s⟩ x x').mpr h

/-- A vertical lens between two types over `Γ`: a base map of shapes over the shapes of `Γ` and a
backward base map of positions. -/
structure TyHom (T T' : Ty Γ) : Type u where
  /-- The forward map on shapes. -/
  fwd : RGraphCwF.Tm (RGraphCwF.ext Γ.A T.S) (T'.S.sub (RGraphCwF.wk T.S))
  /-- The backward map on positions. -/
  back : RGraphCwF.Tm
    (RGraphCwF.ext (RGraphCwF.ext Γ.A T.S)
      (T'.P.sub (RGraphCwF.Hom.comp (RGraphCwF.lift (RGraphCwF.wk T.S) T'.S)
        (RGraphCwF.inst fwd))))
    (T.P.sub (RGraphCwF.wk _))

/-- The lens of a vertical lens at a vertex. -/
def TyHom.fibre {T T' : Ty Γ} (h : TyHom T T') (γ : Γ.A.V) : Lens (T.fibre γ) (T'.fibre γ) :=
  ⟨fun s => h.fwd.V ⟨γ, s⟩, fun s x => h.back.V ⟨⟨γ, s⟩, x⟩⟩

/-- **A vertical lens is a square of signature relations over every edge.** Related shapes go to
related shapes, and related positions go back to related positions. -/
theorem TyHom.square {T T' : Ty Γ} (h : TyHom T T') {γ γ' : Γ.A.V} (e : Γ.A.E γ γ') :
    SigRel.Square (T.edgeRel e) (T'.edgeRel e) (h.fibre γ) (h.fibre γ') where
  shape r := Base.tmE h.fwd e r
  pos {a b} r _ _ hx _ :=
    Base.tmE h.back (γ := ⟨γ, a⟩) (γ' := ⟨γ', b⟩) ⟨e, r⟩ (hx (Base.tmE h.fwd e r))

end Comparison

/-! ## The walking edge -/

/-- The two vertices of the walking edge. -/
inductive WalkV : Type u
  | src
  | tgt

/-- The edges of the walking edge: a reflexive edge at each vertex and one edge from the source to
the target. -/
inductive WalkE : WalkV.{u} → WalkV.{u} → Type u
  | refl (x : WalkV.{u}) : WalkE x x
  | edge : WalkE .src .tgt

/-- The walking edge as a reflexive graph. -/
def walk : RGraphCwF.Ctx.{u} := ⟨WalkV, WalkE, WalkE.refl⟩

section Walk

variable {P Q : PFunctor.{u, u}}

/-- The shapes over the walking edge: `P.A` at the source and `Q.A` at the target. -/
def walkShape (P Q : PFunctor.{u, u}) : WalkV.{u} → Type u
  | .src => P.A
  | .tgt => Q.A

/-- The relation of shapes over an edge of the walking edge. -/
def walkShapeRel (S : SigRel P Q) :
    ∀ {x y : WalkV.{u}}, WalkE x y → walkShape P Q x → walkShape P Q y → Prop
  | _, _, .refl _ => fun a b => a = b
  | _, _, .edge => S.pos

/-- The positions over the walking edge. -/
def walkPos (P Q : PFunctor.{u, u}) : (Σ x : WalkV.{u}, walkShape P Q x) → Type u
  | ⟨.src, a⟩ => P.B a
  | ⟨.tgt, b⟩ => Q.B b

/-- The relation of positions over an edge of the walking edge: heterogeneous equality over a
reflexive edge, the relation of directions over the edge. -/
def walkPosRel (S : SigRel P Q) :
    ∀ {x y : WalkV.{u}}, WalkE x y → (a : walkShape P Q x) → (b : walkShape P Q y) →
      walkPos P Q ⟨x, a⟩ → walkPos P Q ⟨y, b⟩ → Prop
  | _, _, .refl _, _, _ => fun d d' => HEq d d'
  | _, _, .edge, a, b => S.dir a b

/-- The type over the walking edge of a signature relation, in the context without positions. -/
def Ty.ofSigRel (S : SigRel P Q) : Ty (disc walk.{u}) where
  S := ⟨walkShape P Q, walkShapeRel S, fun _ _ _ => Iff.rfl⟩
  P := ⟨walkPos P Q, fun {p q} e => walkPosRel S e.1 p.2 q.2, fun _ _ _ => heq_iff_eq⟩

/-- **Every signature relation is the edge relation of a type over the walking edge**, with the
relation of directions required over related shapes. -/
theorem Ty.edgeRel_ofSigRel (S : SigRel P Q) :
    (Ty.ofSigRel S).edgeRel (Γ := disc walk) WalkE.edge =
      ⟨S.pos, fun a b d d' => S.pos a b → S.dir a b d d'⟩ := rfl

/-- The container at the source of the type of a signature relation is its domain. -/
theorem Ty.fibre_ofSigRel_src (S : SigRel P Q) :
    (Ty.ofSigRel S).fibre (Γ := disc walk) WalkV.src = P := rfl

/-- The container at the target of the type of a signature relation is its codomain. -/
theorem Ty.fibre_ofSigRel_tgt (S : SigRel P Q) :
    (Ty.ofSigRel S).fibre (Γ := disc walk) WalkV.tgt = Q := rfl

variable {P' Q' : PFunctor.{u, u}}

/-- The forward map on shapes over the walking edge of two lenses. -/
def walkFwd (f : Lens P P') (g : Lens Q Q') :
    (p : Σ x : WalkV.{u}, walkShape P Q x) → walkShape P' Q' p.1
  | ⟨.src, a⟩ => f.toFunA a
  | ⟨.tgt, b⟩ => g.toFunA b

/-- The backward map on positions over the walking edge of two lenses. -/
def walkBack (f : Lens P P') (g : Lens Q Q') :
    (p : Σ x : WalkV.{u}, walkShape P Q x) → walkPos P' Q' ⟨p.1, walkFwd f g p⟩ → walkPos P Q p
  | ⟨.src, a⟩, d => f.toFunB a d
  | ⟨.tgt, b⟩, d => g.toFunB b d

/-- The forward map of a square preserves the relations of shapes over every edge. -/
theorem walkFwd_rel {S : SigRel P Q} {S' : SigRel P' Q'} {f : Lens P P'} {g : Lens Q Q'}
    (sq : S.Square S' f g) :
    ∀ {x y : WalkV.{u}} (e : WalkE x y) (a : walkShape P Q x) (b : walkShape P Q y),
      walkShapeRel S e a b → walkShapeRel S' e (walkFwd f g ⟨x, a⟩) (walkFwd f g ⟨y, b⟩)
  | _, _, .refl .src, _, _, r => congrArg f.toFunA r
  | _, _, .refl .tgt, _, _, r => congrArg g.toFunA r
  | _, _, .edge, _, _, r => sq.shape r

/-- The backward map of a square preserves the relations of positions over every edge. -/
theorem walkBack_rel {S : SigRel P Q} {S' : SigRel P' Q'} {f : Lens P P'} {g : Lens Q Q'}
    (sq : S.Square S' f g) :
    ∀ {x y : WalkV.{u}} (e : WalkE x y) (a : walkShape P Q x) (b : walkShape P Q y),
      walkShapeRel S e a b → ∀ d d',
        walkPosRel S' e (walkFwd f g ⟨x, a⟩) (walkFwd f g ⟨y, b⟩) d d' →
        walkPosRel S e a b (walkBack f g ⟨x, a⟩ d) (walkBack f g ⟨y, b⟩ d')
  | _, _, .refl .src, a, _, rfl, _, _, rd => heq_of_eq (congrArg (f.toFunB a) (eq_of_heq rd))
  | _, _, .refl .tgt, b, _, rfl, _, _, rd => heq_of_eq (congrArg (g.toFunB b) (eq_of_heq rd))
  | _, _, .edge, _, _, r, d, d', rd => sq.pos r d d' rd

/-- **A square of signature relations is a vertical lens over the walking edge.** -/
def TyHom.ofSquare {S : SigRel P Q} {S' : SigRel P' Q'} {f : Lens P P'} {g : Lens Q Q'}
    (sq : S.Square S' f g) : TyHom (Γ := disc walk) (Ty.ofSigRel S) (Ty.ofSigRel S') where
  fwd := ⟨walkFwd f g, fun e => walkFwd_rel sq e.1 _ _ e.2⟩
  back := ⟨fun p => walkBack f g p.1 p.2,
    fun {p q} e => walkBack_rel sq e.1.1 p.1.2 q.1.2 e.1.2 p.2 q.2 e.2⟩

/-- The vertical lens of a square has the first lens at the source. -/
theorem TyHom.ofSquare_fibre_src {S : SigRel P Q} {S' : SigRel P' Q'} {f : Lens P P'}
    {g : Lens Q Q'} (sq : S.Square S' f g) : (TyHom.ofSquare sq).fibre WalkV.src = f := rfl

/-- The vertical lens of a square has the second lens at the target. -/
theorem TyHom.ofSquare_fibre_tgt {S : SigRel P Q} {S' : SigRel P' Q'} {f : Lens P P'}
    {g : Lens Q Q'} (sq : S.Square S' f g) : (TyHom.ofSquare sq).fibre WalkV.tgt = g := rfl

end Walk

end CatCrypt.Container.PolyRGraph
