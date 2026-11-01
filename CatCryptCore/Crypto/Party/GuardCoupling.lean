/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Relational.CouplingMass
public import CatCryptCore.Relational.Rules
public import CatCryptCore.Crypto.Party.Call

/-!
# Couplings of guarded computations

The guarded computation `MultiHybrid.guardNF c d` is `c` when `c` never fails and the point
mass at `d` otherwise. A coupling preserves total mass (`rHoare_noFail_iff`), so two
computations related by a relational Hoare triple under `eqPre` have no failure together, and
the two guarded computations take the same branch.

## Main results

* `CatCrypt.Relational.rHoare_guardNF` — a triple under `eqPre` lifts to the guarded
  computations `guardNF c d` and `guardNF c' d'`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.UCTransparent.MultiHybrid

/-- A triple under `eqPre` lifts to the guarded computations: both sides take the same branch
of `guardNF`, the triple's postcondition `Q'` implies `Q` on the unguarded branch, and the
default outputs satisfy `Q` at every heap on the other branch. -/
theorem rHoare_guardNF {β β' : Type} {c : SPComp β} {c' : SPComp β'} {d : β} {d' : β'}
    {Q Q' : RPost β β'} (h : rHoare eqPre c c' Q')
    (hQ : ∀ a h₁ a' h₂, Q' a h₁ a' h₂ → Q a h₁ a' h₂) (hd : ∀ x, Q d x d' x) :
    rHoare eqPre (guardNF c d) (guardNF c' d') Q := by
  by_cases hc : SPComp.NoFail c
  · rw [guardNF_of_noFail d hc, guardNF_of_noFail d' ((rHoare_noFail_iff h).1 hc)]
    exact rHoare_mono_post h hQ
  · have hc' : ¬ SPComp.NoFail c' := fun h' => hc ((rHoare_noFail_iff h).2 h')
    unfold guardNF
    simp only [hc, hc', ite_false]
    exact rHoare_ret fun h₁ h₂ he => by subst he; exact hd h₁

end CatCrypt.Relational
