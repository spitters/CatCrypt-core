/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XPredCore
public import CatCryptCore.XDijkstra.XPostShape

/-!
# Observations pulled back along a monad morphism

A family of maps `h : m α → n α` turns an observation of `n` into an observation of
`m`: the transformer of a program `c : m α` is the transformer of its image `h c`.
When `h` preserves `pure` and `bind`, the pulled-back observation is lawful whenever
the observation of `n` is, and the triples of `c` are the triples of `h c`. A
handler interpreting free-monad syntax into an observed monad is such a morphism, so
the syntax inherits the program logic of the target.

## Main definitions

* `IsMonadMorphism`: a family `m α → n α` preserving `pure` and `bind`.
* `XCoreWP.pullback`: the observation of `m` through `h` and an observation of `n`.
* `XCoreWP.pullbackHom`: `h` as a morphism of observations, with identity maps on
  assertions.
* `XWP.pullback`, `XWP.pullbackMorphism`: the same at the level of post-shapes.

## Main results

* `XCoreWP.lawful_pullback`: the pulled-back observation is lawful when `h` is a monad
  morphism and the observation of `n` is lawful.
* `XCoreWP.pullback_triple_iff`: a triple of `c` under the pulled-back observation is
  a triple of `h c`.
* `XWP.pullback_xtriple_iff`: the same for the shape-level triple.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.XDijkstra

universe u v w x y z

/-- A family of maps `h : m α → n α` that preserves `pure` and `bind`. -/
structure IsMonadMorphism (m : Type x → Type y) (n : Type x → Type z) [Monad m] [Monad n]
    (h : {α : Type x} → m α → n α) : Prop where
  /-- `h` preserves `pure`. -/
  map_pure : ∀ {α : Type x} (a : α), h (pure a : m α) = pure a
  /-- `h` preserves `bind`. -/
  map_bind : ∀ {α β : Type x} (c : m α) (f : α → m β), h (c >>= f) = h c >>= fun a => h (f a)

namespace XCoreWP

variable {m : Type x → Type y} {n : Type x → Type z}
  {Pred : Type u} {EPred : Type v} {G : Type w} [LE Pred] [LE EPred]

/-- The observation of `m` through `h`: the transformer of `c` is the transformer of
`h c` under the observation of `n`. -/
@[reducible] def pullback (h : {α : Type x} → m α → n α) [XCoreWP n Pred EPred G] :
    XCoreWP m Pred EPred G where
  wp c := XCoreWP.wp (h c)

/-- The pulled-back observation is lawful when `h` is a monad morphism and the
observation of `n` is lawful. -/
theorem lawful_pullback [Monad m] [Monad n] [Zero G] [XCoreWP n Pred EPred G]
    [LawfulXCoreWP n Pred EPred] {h : {α : Type x} → m α → n α}
    (hh : IsMonadMorphism m n h) :
    @LawfulXCoreWP m Pred EPred G _ _ _ _ (pullback @h) := by
  let := pullback (Pred := Pred) (EPred := EPred) (G := G) @h
  exact
    { wp_pure := fun a => by
        change (XCoreWP.wp (h (pure a)) : XCorePT Pred EPred G _) = _
        rw [hh.map_pure, LawfulXCoreWP.wp_pure]
      wp_bind := fun c f => by
        change (XCoreWP.wp (h (c >>= f)) : XCorePT Pred EPred G _) = _
        rw [hh.map_bind, LawfulXCoreWP.wp_bind]
        rfl }

/-- Unfolding lemma of `pullback` at the triple: a triple of `c` under the
pulled-back observation is a triple of `h c`. -/
theorem pullback_triple_iff (h : {α : Type x} → m α → n α) [XCoreWP n Pred EPred G]
    {α : Type x} (c : m α) (P : Pred) (post : α → Pred) (epost : EPred) :
    @XCoreWP.Triple m Pred EPred G _ _ (pullback @h) α P c post epost
      ↔ XCoreWP.Triple (m := n) P (h c) post epost :=
  Iff.rfl

/-- `h` is a morphism from the pulled-back observation to the observation of `n`, with
identity maps on preconditions and postconditions. -/
def pullbackHom (h : {α : Type x} → m α → n α) [XCoreWP n Pred EPred G] :
    @XCoreWPHom m n Pred EPred Pred EPred G G _ _ _ _ (pullback @h) _ @h :=
  letI := pullback (Pred := Pred) (EPred := EPred) (G := G) @h
  { postMap := fun Q => Q
    preMap := fun P => P
    preMap_mono := fun hAB => hAB
    transfer := fun _ _ _ => rfl }

end XCoreWP

namespace XWP

variable {Ω : Type u} [Preorder Ω] {m n : Type u → Type v} {ps : XPostShape.{u}}

/-- The shape-level observation of `m` through `h`: the transformer of `c` is the
transformer of `h c` under the observation of `n`. -/
@[reducible] def pullback (h : {α : Type u} → m α → n α) [XWP n ps Ω] : XWP m ps Ω where
  xwp c := XWP.xwp (h c)

/-- Unfolding lemma of `pullback` at the triple: a shape-level triple of `c` under the
pulled-back observation is a triple of `h c`. -/
theorem pullback_xtriple_iff (h : {α : Type u} → m α → n α) [XWP n ps Ω] {α : Type u}
    (P : XAssertion ps Ω) (c : m α) (Q : XPostCond α ps Ω) :
    @XTriple Ω _ m ps α (pullback @h) P c Q ↔ XTriple (m := n) P (h c) Q :=
  Iff.rfl

/-- `h` is a shape-level morphism from the pulled-back observation to the observation
of `n`, with identity maps on preconditions and postconditions. -/
@[instance_reducible] def pullbackMorphism (h : {α : Type u} → m α → n α) [XWP n ps Ω] :
    @XWPMorphism Ω _ m n ps ps (pullback @h) _ @h :=
  letI := pullback (ps := ps) (Ω := Ω) @h
  { postMap := fun Q => Q
    preMap := fun P => P
    preMap_mono := fun hAB => hAB
    transfer := fun _ _ => rfl }

end XWP

end CatCrypt.XDijkstra
