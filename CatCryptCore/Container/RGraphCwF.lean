/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Nat.Notation

/-!
# The reflexive-graph category with families over `Type`

This module gives the relationally parametric model of dependent type theory of Atkey, Ghani and
Johann, as a shallow category with families over `Type u`, in the style of
`CatCryptCore.Container.CwF`.

A context (`Ctx`) is a reflexive graph: vertices `V`, a type of edges `E x y` and a reflexive
edge `refl x`. A substitution (`Hom`) is a morphism of reflexive graphs. A type over `Γ` (`Ty`) is
a family of sets `V γ` over the vertices with, over each edge `e : Γ.E γ γ'`, a relation
`E e : V γ → V γ' → Prop`; over the reflexive edge the relation is equality (`Ty.refl_iff`, the
identity extension condition). A term (`Tm`) is a section `V γ` that sends each edge `e` to a
proof that its values are related over `e`. That last field is Reynolds' abstraction theorem in the
model: every term preserves the relational interpretation (`Tm.abstraction`).

Context extension (`ext`) by a type has the edges of `Γ` paired with relatedness proofs. The
universe of small types is the context extension `extU` whose vertices are pairs of a vertex and a
type `X : Type u` and whose edges carry a relation between the types; its reflexive edge is
equality. `El` is the decoding of the universe, and `Ty.piU` is the dependent product over the
universe. Elements of `Ty.piU B` are the families that preserve every relation; this is the
parametricity condition of Reynolds.

The dependent sum (`Ty.sigma`), the dependent product over a type (`Ty.pi`), the unit
(`Ty.unit`) and discrete types (`Ty.disc`, which give the natural numbers `Ty.nat` and the base
types) are types of the model. All substitution laws, β and η laws of `Ty.sigma`, `Ty.pi` and
`Ty.piU` hold by `rfl`, since edges of types are propositions; the stability of `Ty.piU` under
substitution (`Ty.piU_sub`) holds by propositional extensionality, since the parametricity
condition refers to the reflexive edge of the context, which a substitution preserves only up to
equality.

## Main definitions

* `Ctx`, `Hom`, `Ty`, `Tm`, `Ty.sub`, `Tm.sub` — reflexive graphs, their morphisms, types and
  terms;
* `unit`, `ext`, `wk`, `var`, `extend` — the substitution calculus;
* `Ty.sigma`, `Ty.pi`, `Ty.unit`, `Ty.disc`, `Ty.nat` — type formers;
* `extU`, `El`, `Ty.piU`, `Tm.lamU`, `Tm.appU` — the universe and the product over it.

## Main results

* `wk_extend`, `var_sub_extend`, `extend_wk_var`, `extend_comp` — the comprehension laws;
* `Tm.fst_mkPair`, `Tm.snd_mkPair`, `Tm.app_lam`, `Tm.lam_app`, `Tm.appU_lamU`, `Tm.lamU_appU`
  — β and η;
* `Tm.abstraction`, `Tm.abstractionU` — the abstraction theorem;
* `Tm.polyId_eq` — every closed term of `Π (X : U). X → X` is the identity;
* `Tm.polyConst_eq` — every closed term of `Π (X : U). X → ℕ` is constant.

## References

* R. Atkey, N. Ghani, P. Johann, *A relationally parametric model of dependent type theory*,
  POPL 2014;
* J. C. Reynolds, *Types, abstraction and parametric polymorphism*, IFIP Congress 1983.

Search words: category with families, CwF, reflexive graph, relational parametricity,
abstraction theorem, free theorem, identity extension, logical relation, universe.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container.RGraphCwF

/-- A reflexive graph: vertices, edges and a reflexive edge at each vertex. -/
structure Ctx : Type (u + 1) where
  /-- The vertices. -/
  V : Type u
  /-- The edges between two vertices. -/
  E : V → V → Type u
  /-- The reflexive edge. -/
  refl : ∀ v, E v v

/-- A morphism of reflexive graphs, the substitutions of the model. -/
structure Hom (Δ Γ : Ctx.{u}) : Type u where
  /-- The action on vertices. -/
  map : Δ.V → Γ.V
  /-- The action on edges. -/
  rel : ∀ {x y}, Δ.E x y → Γ.E (map x) (map y)
  /-- Reflexive edges go to reflexive edges. -/
  rel_refl : ∀ x, rel (Δ.refl x) = Γ.refl (map x)

section Category

variable {Γ Δ Θ Ξ : Ctx.{u}}

/-- The identity morphism. -/
def Hom.id (Γ : Ctx.{u}) : Hom Γ Γ where
  map := fun x => x
  rel := fun e => e
  rel_refl := fun _ => rfl

/-- Composition of morphisms, `σ` after `τ`. -/
def Hom.comp (σ : Hom Δ Γ) (τ : Hom Θ Δ) : Hom Θ Γ where
  map := fun x => σ.map (τ.map x)
  rel := fun e => σ.rel (τ.rel e)
  rel_refl := fun x => by rw [τ.rel_refl, σ.rel_refl]

theorem hom_id_comp (σ : Hom Δ Γ) : (Hom.id Γ).comp σ = σ := rfl

theorem hom_comp_id (σ : Hom Δ Γ) : σ.comp (Hom.id Δ) = σ := rfl

theorem hom_comp_assoc (σ : Hom Δ Γ) (τ : Hom Θ Δ) (ρ : Hom Ξ Θ) :
    (σ.comp τ).comp ρ = σ.comp (τ.comp ρ) := rfl

end Category

/-- A type over `Γ`: a family of sets with a relation over each edge, equality over the
reflexive edges. -/
structure Ty (Γ : Ctx.{u}) : Type (u + 1) where
  /-- The set over a vertex. -/
  V : Γ.V → Type u
  /-- The relation over an edge. -/
  E : ∀ {γ γ'}, Γ.E γ γ' → V γ → V γ' → Prop
  /-- Identity extension: the relation over a reflexive edge is equality. -/
  refl_iff : ∀ γ (a b : V γ), E (Γ.refl γ) a b ↔ a = b

/-- A term of `A`: a section that preserves the relations over every edge. -/
structure Tm (Γ : Ctx.{u}) (A : Ty Γ) : Type u where
  /-- The value at a vertex. -/
  V : ∀ γ, A.V γ
  /-- The values at the ends of an edge are related over it. -/
  E : ∀ {γ γ'} (e : Γ.E γ γ'), A.E e (V γ) (V γ')

section Basic

variable {Γ Δ Θ : Ctx.{u}}

/-- The abstraction theorem: a term relates its values at the two ends of every edge. -/
theorem Tm.abstraction {A : Ty Γ} (t : Tm Γ A) {γ γ' : Γ.V} (e : Γ.E γ γ') :
    A.E e (t.V γ) (t.V γ') :=
  t.E e

/-- Substitution in a type. -/
def Ty.sub (A : Ty Γ) (σ : Hom Δ Γ) : Ty Δ where
  V := fun δ => A.V (σ.map δ)
  E := fun e => A.E (σ.rel e)
  refl_iff := fun δ a b => by rw [σ.rel_refl]; exact A.refl_iff _ a b

/-- Substitution in a term. -/
def Tm.sub {A : Ty Γ} (a : Tm Γ A) (σ : Hom Δ Γ) : Tm Δ (A.sub σ) where
  V := fun δ => a.V (σ.map δ)
  E := fun e => a.E (σ.rel e)

theorem Ty.sub_id (A : Ty Γ) : A.sub (Hom.id Γ) = A := rfl

theorem Ty.sub_comp (A : Ty Γ) (τ : Hom Δ Γ) (σ : Hom Θ Δ) :
    (A.sub τ).sub σ = A.sub (τ.comp σ) := rfl

theorem Tm.sub_id {A : Ty Γ} (a : Tm Γ A) : (a.sub (Hom.id Γ) : Tm Γ A) = a := rfl

theorem Tm.sub_comp {A : Ty Γ} (a : Tm Γ A) (τ : Hom Δ Γ) (σ : Hom Θ Δ) :
    ((a.sub τ).sub σ : Tm Θ ((A.sub τ).sub σ)) = a.sub (τ.comp σ) := rfl

end Basic

section Calculus

variable {Γ Δ Θ : Ctx.{u}} {A : Ty Γ}

/-- The terminal reflexive graph. -/
def unit : Ctx.{u} := ⟨PUnit, fun _ _ => PUnit, fun _ => ⟨⟩⟩

/-- The morphism into the terminal graph. -/
def toUnit (Γ : Ctx.{u}) : Hom Γ unit where
  map := fun _ => ⟨⟩
  rel := fun _ => ⟨⟩
  rel_refl := fun _ => rfl

theorem toUnit_unique (σ : Hom Γ unit) : σ = toUnit Γ := rfl

/-- Context extension: vertices are pairs, edges are edges of `Γ` with a relatedness proof. -/
def ext (Γ : Ctx.{u}) (A : Ty Γ) : Ctx.{u} where
  V := Σ γ, A.V γ
  E := fun p q => (e : Γ.E p.1 q.1) ×' A.E e p.2 q.2
  refl := fun p => ⟨Γ.refl p.1, (A.refl_iff _ _ _).mpr rfl⟩

/-- The weakening morphism. -/
def wk (A : Ty Γ) : Hom (ext Γ A) Γ where
  map := Sigma.fst
  rel := PSigma.fst
  rel_refl := fun _ => rfl

/-- The variable. -/
def var (A : Ty Γ) : Tm (ext Γ A) (A.sub (wk A)) where
  V := Sigma.snd
  E := PSigma.snd

/-- The morphism into a context extension given by a morphism and a term. -/
def extend (σ : Hom Δ Γ) (a : Tm Δ (A.sub σ)) : Hom Δ (ext Γ A) where
  map := fun δ => ⟨σ.map δ, a.V δ⟩
  rel := fun e => ⟨σ.rel e, a.E e⟩
  rel_refl := fun x => by
    show PSigma.mk _ _ = PSigma.mk _ _
    congr 1
    exact σ.rel_refl x

/-- Instantiation of the last variable by a term. -/
abbrev inst (a : Tm Γ A) : Hom Γ (ext Γ A) := extend (Hom.id Γ) a

/-- The lifting of a morphism to a context extension. -/
abbrev lift (σ : Hom Δ Γ) (A : Ty Γ) : Hom (ext Δ (A.sub σ)) (ext Γ A) :=
  extend (σ.comp (wk (A.sub σ))) (var (A.sub σ))

theorem wk_extend (σ : Hom Δ Γ) (a : Tm Δ (A.sub σ)) : (wk A).comp (extend σ a) = σ := rfl

theorem var_sub_extend (σ : Hom Δ Γ) (a : Tm Δ (A.sub σ)) :
    ((var A).sub (extend σ a) : Tm Δ (A.sub σ)) = a := rfl

theorem extend_wk_var (A : Ty Γ) : extend (wk A) (var A) = Hom.id (ext Γ A) := rfl

theorem extend_comp (σ : Hom Δ Γ) (a : Tm Δ (A.sub σ)) (τ : Hom Θ Δ) :
    (extend σ a).comp τ = extend (σ.comp τ) (a.sub τ) := rfl

end Calculus

section Formers

variable {Γ Δ : Ctx.{u}} {A : Ty Γ} {B : Ty (ext Γ A)}

/-- The dependent sum. -/
def Ty.sigma (A : Ty Γ) (B : Ty (ext Γ A)) : Ty Γ where
  V := fun γ => Σ a : A.V γ, B.V ⟨γ, a⟩
  E := fun e p q => ∃ r : A.E e p.1 q.1, B.E ⟨e, r⟩ p.2 q.2
  refl_iff := fun γ p q => by
    obtain ⟨a, b⟩ := p
    obtain ⟨a', b'⟩ := q
    constructor
    · rintro ⟨r, s⟩
      obtain rfl := (A.refl_iff γ a a').mp r
      obtain rfl := (B.refl_iff ⟨γ, a⟩ b b').mp s
      rfl
    · rintro ⟨⟩
      exact ⟨(A.refl_iff γ a a).mpr rfl, (B.refl_iff ⟨γ, a⟩ b b).mpr rfl⟩

theorem Ty.sigma_sub (A : Ty Γ) (B : Ty (ext Γ A)) (σ : Hom Δ Γ) :
    (Ty.sigma A B).sub σ = Ty.sigma (A.sub σ) (B.sub (lift σ A)) := rfl

/-- Pairing. -/
def Tm.mkPair (a : Tm Γ A) (b : Tm Γ (B.sub (inst a))) : Tm Γ (Ty.sigma A B) where
  V := fun γ => ⟨a.V γ, b.V γ⟩
  E := fun e => ⟨a.E e, b.E e⟩

/-- The first projection. -/
def Tm.fst (t : Tm Γ (Ty.sigma A B)) : Tm Γ A where
  V := fun γ => (t.V γ).1
  E := fun e => (t.E e).1

/-- The second projection. -/
def Tm.snd (t : Tm Γ (Ty.sigma A B)) : Tm Γ (B.sub (inst (Tm.fst t))) where
  V := fun γ => (t.V γ).2
  E := fun e => (t.E e).2

theorem Tm.fst_mkPair (a : Tm Γ A) (b : Tm Γ (B.sub (inst a))) :
    Tm.fst (Tm.mkPair a b) = a := rfl

theorem Tm.snd_mkPair (a : Tm Γ A) (b : Tm Γ (B.sub (inst a))) :
    Tm.snd (Tm.mkPair a b) = b := rfl

theorem Tm.mkPair_fst_snd (t : Tm Γ (Ty.sigma A B)) : Tm.mkPair (Tm.fst t) (Tm.snd t) = t :=
  rfl

/-- The dependent product: functions on the sets, related when they send related arguments to
related values. -/
def Ty.pi (A : Ty Γ) (B : Ty (ext Γ A)) : Ty Γ where
  V := fun γ => ∀ a : A.V γ, B.V ⟨γ, a⟩
  E := fun e f g => ∀ a a' (r : A.E e a a'), B.E ⟨e, r⟩ (f a) (g a')
  refl_iff := fun γ f g => by
    constructor
    · intro h
      funext a
      exact (B.refl_iff ⟨γ, a⟩ _ _).mp (h a a ((A.refl_iff γ a a).mpr rfl))
    · rintro rfl a a' r
      obtain rfl := (A.refl_iff γ a a').mp r
      exact (B.refl_iff ⟨γ, a⟩ _ _).mpr rfl

theorem Ty.pi_sub (A : Ty Γ) (B : Ty (ext Γ A)) (σ : Hom Δ Γ) :
    (Ty.pi A B).sub σ = Ty.pi (A.sub σ) (B.sub (lift σ A)) := rfl

/-- λ-abstraction. -/
def Tm.lam (t : Tm (ext Γ A) B) : Tm Γ (Ty.pi A B) where
  V := fun γ a => t.V ⟨γ, a⟩
  E := fun {γ γ'} e a a' r => t.E (γ := ⟨γ, a⟩) (γ' := ⟨γ', a'⟩) ⟨e, r⟩

/-- Application, as the inverse of `Tm.lam`. -/
def Tm.app (f : Tm Γ (Ty.pi A B)) : Tm (ext Γ A) B where
  V := fun p => f.V p.1 p.2
  E := fun e => f.E e.1 _ _ e.2

theorem Tm.app_lam (t : Tm (ext Γ A) B) : Tm.app (Tm.lam t) = t := rfl

theorem Tm.lam_app (f : Tm Γ (Ty.pi A B)) : Tm.lam (Tm.app f) = f := rfl

/-- The unit type. -/
def Ty.unit (Γ : Ctx.{u}) : Ty Γ where
  V := fun _ => PUnit
  E := fun _ _ _ => True
  refl_iff := fun _ _ _ => by simp

/-- The discrete type on a set: the same set everywhere, equality over every edge. -/
def Ty.disc (Γ : Ctx.{u}) (X : Type u) : Ty Γ where
  V := fun _ => X
  E := fun _ a b => a = b
  refl_iff := fun _ _ _ => Iff.rfl

/-- The natural numbers. -/
abbrev Ty.nat (Γ : Ctx.{u}) : Ty Γ := Ty.disc Γ (ULift ℕ)

/-- A constant term of a discrete type. -/
def Tm.const {X : Type u} (x : X) : Tm Γ (Ty.disc Γ X) where
  V := fun _ => x
  E := fun _ => rfl

/-- A function between sets as a term of the product of discrete types. -/
def Tm.discFun {X Y : Type u} (f : X → Y) : Tm Γ (Ty.pi (Ty.disc Γ X) (Ty.disc _ Y)) where
  V := fun _ => f
  E := fun _ _ _ r => congrArg f r

end Formers

section Universe

variable {Γ Δ : Ctx.{u + 1}}

/-- Context extension by the universe of small types: a vertex carries a type, an edge carries a
relation between the types, and the reflexive edge carries equality. -/
def extU (Γ : Ctx.{u + 1}) : Ctx.{u + 1} where
  V := Γ.V × Type u
  E := fun p q => Γ.E p.1 q.1 × (p.2 → q.2 → Prop)
  refl := fun p => (Γ.refl p.1, fun a b => a = b)

/-- Weakening of the universe variable. -/
def wkU (Γ : Ctx.{u + 1}) : Hom (extU Γ) Γ where
  map := Prod.fst
  rel := Prod.fst
  rel_refl := fun _ => rfl

/-- The lifting of a morphism to the extension by the universe. -/
def liftU (σ : Hom Δ Γ) : Hom (extU Δ) (extU Γ) where
  map := fun p => (σ.map p.1, p.2)
  rel := fun e => (σ.rel e.1, e.2)
  rel_refl := fun _ => Prod.ext (σ.rel_refl _) rfl

/-- The decoding of the universe variable: the type it names, related by the relation of the
edge. -/
def El (Γ : Ctx.{u + 1}) : Ty (extU Γ) where
  V := fun p => ULift.{u + 1} p.2
  E := fun e a b => e.2 a.down b.down
  refl_iff := fun _ _ _ => ULift.ext_iff.symm

/-- The dependent product over the universe: the families that preserve every relation between
small types. -/
def Ty.piU (B : Ty (extU Γ)) : Ty Γ where
  V := fun γ => {f : ∀ X : Type u, B.V (γ, X) //
    ∀ (X Y : Type u) (R : X → Y → Prop), B.E (Γ.refl γ, R) (f X) (f Y)}
  E := fun e f g => ∀ (X Y : Type u) (R : X → Y → Prop), B.E (e, R) (f.1 X) (g.1 Y)
  refl_iff := fun γ f g => by
    constructor
    · intro h
      exact Subtype.ext (funext fun X => (B.refl_iff (γ, X) _ _).mp (h X X Eq))
    · rintro rfl
      exact f.2

/-- λ-abstraction over the universe. -/
def Tm.lamU {B : Ty (extU Γ)} (t : Tm (extU Γ) B) : Tm Γ (Ty.piU B) where
  V := fun γ => ⟨fun X => t.V (γ, X),
    fun X Y R => t.E (γ := (γ, X)) (γ' := (γ, Y)) (Γ.refl γ, R)⟩
  E := fun {γ γ'} e X Y R => t.E (γ := (γ, X)) (γ' := (γ', Y)) (e, R)

/-- Application to the universe variable. -/
def Tm.appU {B : Ty (extU Γ)} (f : Tm Γ (Ty.piU B)) : Tm (extU Γ) B where
  V := fun p => (f.V p.1).1 p.2
  E := fun e => f.E e.1 _ _ e.2

theorem Tm.appU_lamU {B : Ty (extU Γ)} (t : Tm (extU Γ) B) : Tm.appU (Tm.lamU t) = t := rfl

theorem Tm.lamU_appU {B : Ty (extU Γ)} (f : Tm Γ (Ty.piU B)) : Tm.lamU (Tm.appU f) = f := rfl

/-- The abstraction theorem at the universe (Reynolds): the value of a term of `Π (X : U). B` at
a vertex sends every relation between small types to a relation over it. -/
theorem Tm.abstractionU {B : Ty (extU Γ)} (t : Tm Γ (Ty.piU B)) (γ : Γ.V) (X Y : Type u)
    (R : X → Y → Prop) : B.E (Γ.refl γ, R) ((t.V γ).1 X) ((t.V γ).1 Y) :=
  (t.V γ).2 X Y R

/-- The type `Π (X : U). X → X`. -/
def polyIdTy : Ty (unit.{u + 1}) :=
  Ty.piU (Ty.pi (El unit) ((El unit).sub (wk (El unit))))

/-- Every closed term of `Π (X : U). X → X` is the identity. -/
theorem Tm.polyId_eq (t : Tm unit polyIdTy.{u}) (X : Type u) (x : X) :
    ((t.V ⟨⟩).1 X ⟨x⟩).down = x :=
  (t.V ⟨⟩).2 X PUnit (fun a _ => a = x) ⟨x⟩ ⟨⟨⟩⟩ rfl

/-- The type `Π (X : U). X → ℕ`. -/
def polyConstTy : Ty (unit.{u + 1}) :=
  Ty.piU (Ty.pi (El unit) (Ty.nat _))

/-- Every closed term of `Π (X : U). X → ℕ` is constant: its values at any two small types and
any two arguments agree. -/
theorem Tm.polyConst_eq (t : Tm unit polyConstTy.{u}) (X Y : Type u) (x : X) (y : Y) :
    (t.V ⟨⟩).1 X ⟨x⟩ = (t.V ⟨⟩).1 Y ⟨y⟩ :=
  (t.V ⟨⟩).2 X Y (fun _ _ => True) ⟨x⟩ ⟨y⟩ trivial

end Universe

end CatCrypt.Container.RGraphCwF
