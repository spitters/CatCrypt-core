/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.PriceSound
public import CatCryptCore.Container.DNRel
public import Mathlib.Logic.Relation

/-!
# Transport of price-soundness along changes of representation

Price-soundness (`DNLens.PriceSound`) relates a Diller–Nahm morphism of clock objects, the
specification, to a closure into `CTree`, the implementation, at relations of arguments and
results. This module transports it along a change of either side.

On the implementation side a change of representation is a relation `R₂` of argument values
with trees that are leaves after at most as many ticks, at related values (`CTree.SimLE`). The
composite relations `Relation.Comp R R₂` and `Relation.Comp S S₂` then relate the specification to
the new closure (`DNLens.PriceSound.impl`). On the specification side a change is a square of
Diller–Nahm morphisms over clock relations (`SigRel.DNSquare` at `SigRel.clock`): related shapes
demand equal multisets of tokens, so the bound carries over to the related morphism
(`DNLens.PriceSound.spec`).

`CTree.SimLE` is reflexive, composes along `Relation.Comp`, and is preserved by `bind`, so that
the hypotheses of the implementation transport compose with the composition of the gluing
`PriceObj`. A morphism of the gluing transports along both changes at once
(`PriceHom.transport`) between the transported objects (`PriceObj.transport`).

## Main definitions

* `CTree.SimLE` — a tree is a leaf after at most the ticks of another, at a related value;
* `PriceObj.transport`, `PriceHom.transport` — objects and morphisms of the gluing along a
  change of specification and of implementation.

## Main results

* `CTree.SimLE.refl`, `CTree.SimLE.trans`, `CTree.SimLE.bind`;
* `DNLens.PriceSound.impl` — transport along a change of the implementation;
* `DNLens.PriceSound.spec` — transport along a square of specifications;
* `DNLens.KeepsTokens.of_dnSquare` — keeping tokens transports along a square.

## References

* N. Danner, D. R. Licata, R. Ramyaa, *Denotational cost semantics for functional languages with
  inductive types*, ICFP 2015;
* J. C. Mitchell, A. Scedrov, *Notes on sconing and relators*, CSL 1992;
* J. C. Reynolds, *Types, abstraction and parametric polymorphism*, IFIP 1983.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Container

/-! ## Tick simulation of trees -/

/-- A tree is a leaf after at most the ticks of another: whenever `t` is a leaf `w` after `m`
ticks, `t'` is a leaf `w'` after at most `m` ticks, with `S w w'`. -/
def CTree.SimLE {Y' Y'' : Type} (S : Y' → Y'' → Prop) (t : CTree Y') (t' : CTree Y'') : Prop :=
  ∀ m w, t = stepN CTree.tick m (.ret w) →
    ∃ m' w', t' = stepN CTree.tick m' (.ret w') ∧ m' ≤ m ∧ S w w'

/-- A bind that is a leaf after `m` ticks splits into a leaf of the tree after `a` ticks and a
leaf of the continuation after `b` ticks, with `a + b = m`. -/
theorem CTree.bind_eq_stepN_tick_ret {α β : Type} {k : α → CTree β} {z : β} :
    ∀ (m : ℕ) (t : CTree α), t.bind k = stepN CTree.tick m (.ret z) →
      ∃ a w b, t = stepN CTree.tick a (.ret w) ∧ k w = stepN CTree.tick b (.ret z) ∧ a + b = m
  | m, .ret w, h => ⟨0, w, m, rfl, h, Nat.zero_add m⟩
  | 0, .tick _, h => by cases h
  | m + 1, .tick t, h => by
    obtain ⟨a, w, b, h1, h2, h3⟩ := CTree.bind_eq_stepN_tick_ret m t (CTree.tick.inj h)
    exact ⟨a + 1, w, b, by rw [h1]; rfl, h2, by omega⟩
  | m, .sample _ _, h => by cases m <;> cases h
  | m, .get _ _ _, h => by cases m <;> cases h
  | m, .set _ _ _ _, h => by cases m <;> cases h
  | m, .query _ _ _ _, h => by cases m <;> cases h
  | m, .fail, h => by cases m <;> cases h

namespace CTree.SimLE

variable {Y Y' Y'' Z Z' : Type}

/-- Every tree simulates itself at a reflexive relation. -/
theorem refl {S : Y → Y → Prop} (hS : ∀ y, S y y) (t : CTree Y) : CTree.SimLE S t t :=
  fun m w h => ⟨m, w, h, le_rfl, hS w⟩

/-- Simulations compose along the composite relation. -/
theorem trans {S : Y → Y' → Prop} {S' : Y' → Y'' → Prop} {t : CTree Y} {t' : CTree Y'}
    {t'' : CTree Y''} (h : CTree.SimLE S t t') (h' : CTree.SimLE S' t' t'') :
    CTree.SimLE (Relation.Comp S S') t t'' := by
  intro m w ht
  obtain ⟨m', w', ht', hm', hw'⟩ := h m w ht
  obtain ⟨m'', w'', ht'', hm'', hw''⟩ := h' m' w' ht'
  exact ⟨m'', w'', ht'', hm''.trans hm', w', hw', hw''⟩

/-- Simulation is preserved by `bind` with continuations that simulate each other at related
values. -/
theorem bind {S : Y → Y' → Prop} {T : Z → Z' → Prop} {t : CTree Y} {t' : CTree Y'}
    {k : Y → CTree Z} {k' : Y' → CTree Z'} (h : CTree.SimLE S t t')
    (hk : ∀ w w', S w w' → CTree.SimLE T (k w) (k' w')) :
    CTree.SimLE T (t.bind k) (t'.bind k') := by
  intro m z hz
  obtain ⟨a, w, b, ha, hb, hab⟩ := CTree.bind_eq_stepN_tick_ret m t hz
  obtain ⟨a', w', ha', haa, hww⟩ := h a w ha
  obtain ⟨b', z', hb', hbb, hzz⟩ := hk w w' hww b z hb
  refine ⟨a' + b', z', ?_, by omega, hzz⟩
  rw [ha', stepN_tick_bind, CTree.bind_ret, hb', stepN_add]

end CTree.SimLE

/-! ## Transport of price-soundness -/

namespace DNLens

variable {X X' X'' X₀ Y Y' Y'' Y₀ : Type}

/-- Transport along a change of the implementation: a closure `g'` on another representation,
whose trees at related arguments are leaves after at most the ticks of those of `g`, is bounded at
the composite relations. -/
theorem PriceSound.impl {R : X → X' → Prop} {S : Y → Y' → Prop} {R₂ : X' → X'' → Prop}
    {S₂ : Y' → Y'' → Prop} {F : DNLens (clockPos X) (clockPos Y)} {g : X' → CTree Y'}
    {g' : X'' → CTree Y''} (hF : PriceSound R S F g)
    (hg : ∀ v w, R₂ v w → CTree.SimLE S₂ (g v) (g' w)) :
    PriceSound (Relation.Comp R R₂) (Relation.Comp S S₂) F g' := by
  rintro u w ⟨v, huv, hvw⟩
  obtain ⟨m, y, hy, hm, hS⟩ := hF u v huv
  obtain ⟨m', y', hy', hm', hS₂⟩ := hg v w hvw m y hy
  exact ⟨m', y', hy', hm'.trans hm, y, hS, hS₂⟩

/-- Transport along a related specification with equal demands: a square of Diller–Nahm
morphisms over clock relations carries the bound of `F` to `F₀`. -/
theorem PriceSound.spec {R₀ : X₀ → X → Prop} {S₀ : Y₀ → Y → Prop} {R : X → X' → Prop}
    {S : Y → Y' → Prop} {F₀ : DNLens (clockPos X₀) (clockPos Y₀)}
    {F : DNLens (clockPos X) (clockPos Y)} {g : X' → CTree Y'}
    (hsq : SigRel.DNSquare (SigRel.clock R₀) (SigRel.clock S₀) F₀ F)
    (hF : PriceSound R S F g) :
    PriceSound (Relation.Comp R₀ R) (Relation.Comp S₀ S) F₀ g := by
  rintro u₀ v ⟨u, hu₀, huv⟩
  obtain ⟨m, y, hy, hm, hS⟩ := hF u v huv
  have he : F₀.toFunB u₀ false = F.toFunB u false :=
    Multiset.rel_eq.1 (hsq.pos hu₀ false false rfl)
  exact ⟨m, y, hy, he ▸ hm, F.toFunA u, hsq.shape hu₀, hS⟩

/-- Keeping tokens transports along a square of clock relations whose relation of arguments
relates every argument of `F₀`. -/
theorem KeepsTokens.of_dnSquare {R₀ : X₀ → X → Prop} {S₀ : Y₀ → Y → Prop}
    {F₀ : DNLens (clockPos X₀) (clockPos Y₀)} {F : DNLens (clockPos X) (clockPos Y)}
    (hsq : SigRel.DNSquare (SigRel.clock R₀) (SigRel.clock S₀) F₀ F)
    (htot : ∀ u₀, ∃ u, R₀ u₀ u) (hF : KeepsTokens F) : KeepsTokens F₀ := by
  intro u₀
  obtain ⟨u, hu⟩ := htot u₀
  have he : ∀ d, F₀.toFunB u₀ d = F.toFunB u d := fun d =>
    Multiset.rel_eq.1 (hsq.pos hu d d rfl)
  rw [he, he]
  exact hF u

end DNLens

/-! ## Transport in the gluing -/

/-- The object of the gluing along a change of the shapes by `R₀` and of the values by `R₂`. -/
def PriceObj.transport (A : PriceObj) {X₀ X'' : Type} (R₀ : X₀ → A.X → Prop)
    (R₂ : A.X' → X'' → Prop) : PriceObj :=
  ⟨X₀, X'', Relation.Comp R₀ (Relation.Comp A.R R₂)⟩

/-- A morphism of the gluing transports along a square of specifications and a simulation of
implementations, between the transported objects. -/
def PriceHom.transport {A B : PriceObj} (f : PriceHom A B) {X₀ X'' Y₀ Y'' : Type}
    {R₀ : X₀ → A.X → Prop} {S₀ : Y₀ → B.X → Prop} {R₂ : A.X' → X'' → Prop}
    {S₂ : B.X' → Y'' → Prop} (F₀ : DNLens (clockPos X₀) (clockPos Y₀))
    (hsq : SigRel.DNSquare (SigRel.clock R₀) (SigRel.clock S₀) F₀ f.F)
    (hk : DNLens.KeepsTokens F₀) (g' : X'' → CTree Y'')
    (hg : ∀ v w, R₂ v w → CTree.SimLE S₂ (f.g v) (g' w)) :
    PriceHom (A.transport R₀ R₂) (B.transport S₀ S₂) where
  F := F₀
  g := g'
  keeps := hk
  sound := DNLens.PriceSound.spec hsq (DNLens.PriceSound.impl f.sound hg)

end CatCrypt.Complexity.D
