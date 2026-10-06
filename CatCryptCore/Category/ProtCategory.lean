/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad
public import Mathlib.CategoryTheory.Category.Basic

/-!
# Mathlib Category Instance for Generic ProtObj

This file registers a `Category` instance for `UCMonad.ProtObj T hon out`, the generic
protocol category parameterized over any monad `T` satisfying `UCMonadBase`.

The categorical laws (`id_comp`, `comp_id`, `assoc`) are already proved in `UCMonad.lean`
as standalone lemmas on the `.sim` field. Here we lift them through an extensionality
lemma (the `comm` field is `Prop`, hence proof-irrelevant) to get the full `Category` instance.

## Main results

* `ProtMor.ext` — extensionality: two morphisms are equal iff their `.sim` fields agree
* `Category (ProtObj T hon out)` — Mathlib category instance
* `comp_sim`, `id_sim` — `@[simp]` lemmas bridging categorical notation to definitions
-/

@[expose] public section

namespace UCMonad

open CategoryTheory

variable {T : Type → Type} [UCMonadBase T] {hon out : Type}

/-- Two protocol morphisms are equal iff their simulator fields agree.
    The `comm` field is `Prop`, so it is proof-irrelevant. -/
@[ext]
theorem ProtMor.ext {P Q : ProtObj T hon out}
    {f g : ProtMor P Q} (h : f.sim = g.sim) : f = g := by
  rcases f with ⟨fs, fc⟩; rcases g with ⟨gs, gc⟩
  subst h; rfl

noncomputable instance : CategoryStruct (ProtObj T hon out) where
  Hom := ProtMor
  id := protMor_id
  comp := protMor_comp

noncomputable instance : Category (ProtObj T hon out) where
  id_comp f := ProtMor.ext (protMor_comp_id_left f)
  comp_id f := ProtMor.ext (protMor_comp_id_right f)
  assoc f g h := ProtMor.ext (protMor_comp_assoc f g h)

variable {P Q R : ProtObj T hon out}

@[simp]
theorem comp_sim (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).sim = fun x => f.sim x >>= g.sim := rfl

@[simp]
theorem id_sim : (𝟙 P : P ⟶ P).sim = pure := rfl

end UCMonad
