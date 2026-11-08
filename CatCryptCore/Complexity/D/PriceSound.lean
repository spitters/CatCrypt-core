/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.PolyModel
public import Mathlib.CategoryTheory.Category.Basic

/-!
# The price-sound gluing of the Diller–Nahm category along `CTree`

A Diller–Nahm morphism `F` of clock objects `clockPos X ⟶ clockPos Y` bounds a closure
`g : X' → CTree Y'` at relations `R : X → X' → Prop` and `S : Y → Y' → Prop`
(`DNLens.PriceSound`) when, at related arguments `R u v`, the tree `g v` is a leaf after at most
the clock ticks that a data token of the output demands at `u`, at a value related by `S` to the
forward map at `u`. This is the bounding relation of Danner, Licata and Ramyaa between a cost
semantics and an operational semantics, here between the Diller–Nahm model and the step-counting
trees of D.

The objects of `PriceObj` are pairs of types with a relation, and its morphisms (`PriceHom`) are
a Diller–Nahm morphism, a closure and the bound, where the morphism keeps tokens
(`DNLens.KeepsTokens`: a data token demands a data token and a clock tick a clock tick). The
category is the gluing (sconing) of the Diller–Nahm category of clock objects along the Kleisli
category of `CTree`; composition binds the closures (`DNLens.PriceSound.comp`). Without the
condition on tokens the bound is not closed under composition: a consumer that demands no data
token of its input does not pay for the steps of the producer.

D's logical relation `Sim` at a function type is price-soundness of the morphism of the costed
closure (`Sim.arr_iff_priceSound`), so that a related closure is a morphism of the gluing
(`Ty.priceHomOfSim`), and a pure term of the fragment in related environments is a morphism
(`Tm.priceHom`) whose bound is the soundness theorem `Tm.dtC_timedSim` at the abstraction of the
term (`Tm.priceSound_dnC`).

## Main definitions

* `DNLens.PriceSound`, `DNLens.KeepsTokens`
* `PriceObj`, `PriceHom`, the category instance on `PriceObj`
* `Ty.priceObj`, `Ty.priceHomOfSim`, `Tm.priceHom`

## Main results

* `DNLens.PriceSound.id`, `DNLens.PriceSound.comp`: identity and composition
* `Sim.arr_iff_priceSound`: `Sim` at a function type is an instance of price-soundness
* `Tm.priceSound_dnC`: the Diller–Nahm morphism of a pure term bounds its evaluation

## References

* N. Danner, D. R. Licata, R. Ramyaa, *Denotational cost semantics for functional languages with
  inductive types*, ICFP 2015;
* G. A. Kavvos, E. Morehouse, D. R. Licata, N. Danner, *Recurrence extraction for functional
  programs through call-by-push-value*, POPL 2020;
* J. C. Mitchell, A. Scedrov, *Notes on sconing and relators*, CSL 1992;
* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Container

/-! ## Counting tokens in a bind -/

/-- The multiplicity of a token in a bind of token multisets: the data tokens of `M` times the
multiplicity in `f false`, plus the clock ticks of `M` times the multiplicity in `f true`. -/
theorem count_bind_bool (M : Multiset Bool) (f : Bool → Multiset Bool) (c : Bool) :
    (M.bind f).count c = M.count false * (f false).count c + M.count true * (f true).count c := by
  conv_lhs => rw [multiset_bool_decomp M]
  simp [Multiset.add_bind, nsmul_bind, Multiset.count_nsmul]

/-! ## Price-soundness -/

/-- A Diller–Nahm morphism of clock objects bounds a closure at the relations `R`, `S`: at related
arguments the closure is a leaf after at most the ticks a data token demands, at a value related to
the forward map. -/
def DNLens.PriceSound {X Y X' Y' : Type} (R : X → X' → Prop) (S : Y → Y' → Prop)
    (F : DNLens (clockPos X) (clockPos Y)) (g : X' → CTree Y') : Prop :=
  ∀ u v, R u v → ∃ m w, g v = stepN CTree.tick m (.ret w) ∧
    m ≤ (F.toFunB u false).count true ∧ S (F.toFunA u) w

/-- A Diller–Nahm morphism of clock objects keeps tokens: a data token demands at least one data
token, and a clock tick at least one clock tick. -/
def DNLens.KeepsTokens {X Y : Type} (F : DNLens (clockPos X) (clockPos Y)) : Prop :=
  ∀ a, 1 ≤ (F.toFunB a false).count false ∧ 1 ≤ (F.toFunB a true).count true

namespace DNLens

variable {X Y Z X' Y' Z' : Type}

/-- The identity keeps tokens. -/
theorem KeepsTokens.id : KeepsTokens (DNLens.id (clockPos X)) := fun _ => by
  simp [DNLens.id]

/-- A composite of morphisms that keep tokens keeps tokens. -/
theorem KeepsTokens.comp {F : DNLens (clockPos X) (clockPos Y)}
    {G : DNLens (clockPos Y) (clockPos Z)} (hF : KeepsTokens F) (hG : KeepsTokens G) :
    KeepsTokens (DNLens.comp G F) := fun a => by
  simp only [DNLens.comp, count_bind_bool]
  obtain ⟨h1, h2⟩ := hF a
  obtain ⟨h3, h4⟩ := hG (F.toFunA a)
  constructor <;> nlinarith

/-- A linear morphism, the morphism of a costed function, keeps tokens. -/
theorem KeepsTokens.of_isLinear {F : DNLens (clockPos X) (clockPos Y)}
    (hF : Costed.IsLinear F) : KeepsTokens F := fun a => by
  obtain ⟨c, hc⟩ := hF.2 a
  simp [hc, hF.1 a]

/-- The identity bounds the return of the argument. -/
theorem PriceSound.id (R : X → X' → Prop) :
    PriceSound R R (DNLens.id (clockPos X)) CTree.ret :=
  fun _ v h => ⟨0, v, rfl, Nat.zero_le _, h⟩

/-- Composition: if `F` bounds `g` and `G` bounds `k`, the composite bounds the bind of `g` and
`k`, when a clock tick demands a clock tick of `F` and a data token a data token of `G`. -/
theorem PriceSound.comp {R : X → X' → Prop} {S : Y → Y' → Prop} {T : Z → Z' → Prop}
    {F : DNLens (clockPos X) (clockPos Y)} {G : DNLens (clockPos Y) (clockPos Z)}
    {g : X' → CTree Y'} {k : Y' → CTree Z'}
    (hFt : ∀ a, 1 ≤ (F.toFunB a true).count true)
    (hGd : ∀ b, 1 ≤ (G.toFunB b false).count false)
    (hF : PriceSound R S F g) (hG : PriceSound S T G k) :
    PriceSound R T (DNLens.comp G F) (fun v => (g v).bind k) := by
  intro u v huv
  obtain ⟨m₁, w₁, he₁, hm₁, hw₁⟩ := hF u v huv
  obtain ⟨m₂, w₂, he₂, hm₂, hw₂⟩ := hG _ _ hw₁
  refine ⟨m₁ + m₂, w₂, ?_, ?_, hw₂⟩
  · change (g v).bind k = _
    rw [he₁, stepN_tick_bind, CTree.bind_ret, he₂, stepN_add]
  · have h₁ := hFt u
    have h₂ := hGd (F.toFunA u)
    simp only [DNLens.comp, count_bind_bool]
    nlinarith

end DNLens

/-! ## The gluing -/

/-- An object of the gluing: the shapes `X` of a clock object, the values `X'` of the operational
model, and a relation between them. -/
structure PriceObj where
  /-- The shapes of the clock object. -/
  X : Type
  /-- The values of the operational model. -/
  X' : Type
  /-- The relation between shapes and values. -/
  R : X → X' → Prop

/-- A morphism of the gluing: a Diller–Nahm morphism that keeps tokens and a closure into `CTree`,
the morphism bounding the closure. -/
@[ext]
structure PriceHom (A B : PriceObj) where
  /-- The Diller–Nahm morphism. -/
  F : DNLens (clockPos A.X) (clockPos B.X)
  /-- The closure of the operational model. -/
  g : A.X' → CTree B.X'
  /-- A data token demands a data token, a clock tick a clock tick. -/
  keeps : DNLens.KeepsTokens F
  /-- The morphism bounds the closure. -/
  sound : DNLens.PriceSound A.R B.R F g

namespace PriceObj

open CategoryTheory

instance instCategory : Category PriceObj where
  Hom := PriceHom
  id A := ⟨DNLens.id _, CTree.ret, DNLens.KeepsTokens.id, DNLens.PriceSound.id A.R⟩
  comp f h := ⟨DNLens.comp h.F f.F, fun v => (f.g v).bind h.g, f.keeps.comp h.keeps,
    DNLens.PriceSound.comp (fun a => (f.keeps a).2) (fun b => (h.keeps b).1) f.sound h.sound⟩
  id_comp _ := PriceHom.ext (DNLens.comp_id _) (funext fun _ => CTree.bind_ret _ _)
  comp_id _ := PriceHom.ext (DNLens.id_comp _) (funext fun _ => CTree.bind_ret_right _)
  assoc _ _ _ :=
    PriceHom.ext (DNLens.comp_assoc _ _ _).symm (funext fun _ => CTree.bind_assoc _ _ _)

end PriceObj

/-! ## D in the gluing -/

/-- The object of the gluing of a type of D: its translated values, its values and `Sim`. -/
def Ty.priceObj (τ : Ty) : PriceObj := ⟨τ.hat, Val τ, Sim τ⟩

/-- `Sim` at a function type is price-soundness of the costed closure's morphism. -/
theorem Sim.arr_iff_priceSound {a b : Ty} {p : Ty.hat (.arr a b)} {g : Val (.arr a b)} :
    Sim (.arr a b) p g ↔ DNLens.PriceSound (Sim a) (Sim b) (Costed.toDN p) g :=
  Sim.arr_iff_demand

/-- A costed closure related to a function of D is a morphism of the gluing. -/
def Ty.priceHomOfSim {a b : Ty} {p : Ty.hat (.arr a b)} {g : Val (.arr a b)}
    (h : Sim (.arr a b) p g) : PriceHom a.priceObj b.priceObj :=
  ⟨Costed.toDN p, g, DNLens.KeepsTokens.of_isLinear (Costed.isLinear_toDN p),
    Sim.arr_iff_priceSound.1 h⟩

namespace Tm

variable {Γ : List Ty} {σ τ : Ty}

/-- The Diller–Nahm morphism of a pure term of the fragment, in related environments, bounds its
evaluation: the soundness theorem `dtC_timedSim` at the abstraction of the term, read through
`Sim.arr_iff_priceSound`. -/
theorem priceSound_dnC (cc : Ty → ℕ) (hcc : ∀ a, cc a ≤ 1) (t : Tm (σ :: Γ) τ)
    (ht : t.InDtFrag) (hp : t.Pure) {η : EnvHat Γ} {ρ : Env Γ} (hρ : SimEnv η ρ) :
    DNLens.PriceSound (Sim σ) (Sim τ) (t.dnC cc η) (fun v => t.eval (ρ.cons v)) := by
  have h : TimedSimTree (Sim (.arr σ τ)) 1 _ (.ret (t.costedC cc η))
      (.ret fun v => t.eval (ρ.cons v)) := dtC_timedSim cc hcc (Tm.lam t) ⟨ht, hp⟩ hρ
  cases h with
  | ret hs => exact Sim.arr_iff_priceSound.1 hs

/-- The functor of the pure fragment lands in the gluing: a pure term of the fragment, in related
environments, is a morphism from the object of its variable to the object of its type. -/
noncomputable def priceHom (cc : Ty → ℕ) (hcc : ∀ a, cc a ≤ 1) (t : Tm (σ :: Γ) τ)
    (ht : t.InDtFrag) (hp : t.Pure) {η : EnvHat Γ} {ρ : Env Γ} (hρ : SimEnv η ρ) :
    PriceHom σ.priceObj τ.priceObj :=
  ⟨t.dnC cc η, fun v => t.eval (ρ.cons v),
    DNLens.KeepsTokens.of_isLinear (Costed.isLinear_toDN _), priceSound_dnC cc hcc t ht hp hρ⟩

end Tm

end CatCrypt.Complexity.D
