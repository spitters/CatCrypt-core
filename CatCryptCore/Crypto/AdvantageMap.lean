/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage

/-!
# Advantage of mapped games

Mapping two games by the same function `f` and distinguishing them with `D` is distinguishing
the unmapped games with `D ∘ f`.

## Main results

* `advantageA_map` — `AdvantageA (G.map f) (H.map f) D = AdvantageA G H (D ∘ f)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

open CatCrypt.Core

/-- A game followed by `f` and the distinguisher `D` is the game followed by `D ∘ f`. -/
theorem map_bind_eq {α β γ : Type*} (G : SPComp α) (f : α → β) (D : β → SPComp γ) :
    (G.map f).bind D = G.bind (D ∘ f) := by
  simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, Function.comp_def]

/-- The advantage of `D` between two games mapped by `f` is the advantage of `D ∘ f` between
the games. -/
theorem advantageA_map {α β : Type*} (G H : SPComp α) (f : α → β) (D : β → SPComp Bool) :
    AdvantageA (G.map f) (H.map f) D = AdvantageA G H (D ∘ f) := by
  simp only [AdvantageA, map_bind_eq]

end CatCrypt.Crypto
