/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.KEMDEM
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Time of the KEM/DEM reductions

The computation trees and costed forms of the three hop reductions `ReductionKEM1`,
`ReductionDEM` and `ReductionKEM2` of `CatCryptCore.Examples.KEMDEM`, derived by
`derive_reduction`, and their time bounds.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per bookkeeping step; the DEM
encryption is a data primitive with cost companion `encCost`; the KEM key generation and
encapsulation are computation primitives (costed trees, encapsulation with call cost
`encapCost`); the distinguisher call costs its cost companion.

## Main results

* `ReductionKEM1.tree.timeBound_timed`, `ReductionKEM2.tree.timeBound_timed` — time at most
  `T + a + te + 2` for a distinguisher of time `T`, call cost `a` and an encryption of cost
  at most `te`
* `ReductionDEM.tree.timeBound_timed` — time at most `tk + tE + te + T + a + 2` with key
  generation of time `tk`, encapsulation of time `tE` and call cost `te`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.KEMDEM

open CatCrypt.Core

derive_reduction ReductionKEM1

derive_reduction ReductionDEM

derive_reduction ReductionKEM2

/-- **Time of the first KEM hop.** A distinguisher `A` of time at most `T` and call cost at most
`a`, with a DEM encryption of cost at most `te`, gives a reduction of time at most
`T + a + te + 2`. -/
theorem ReductionKEM1.tree.timeBound_timed {PKey Key EKey Plain Cipher : Type}
    (DEM : DEMScheme Key Plain Cipher) (m : Plain)
    (A : PKey × EKey × Cipher → SPTree.Timed Bool) (ACost : PKey × EKey × Cipher → ℕ)
    (enc : Key → Plain → Cipher) (encCost : Key → Plain → ℕ) {T a te : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (he : ∀ k p, encCost k p ≤ te)
    (c : PKey × EKey × Key) :
    SPTree.Timed.stepTime (ReductionKEM1.tree.timed DEM m A ACost c enc encCost) ≤
      T + a + te + 2 := by
  time_bound

/-- **Time of the DEM hop.** A distinguisher `A` of time at most `T` and call cost at most `a`,
with key generation of time at most `tk` and encapsulation of time at most `tE` and call cost
at most `te`, gives a reduction of time at most `tk + tE + te + T + a + 2`. -/
theorem ReductionDEM.tree.timeBound_timed {PKey SKey Key EKey Cipher : Type}
    (KEM : KEMScheme PKey SKey Key EKey)
    (A : PKey × EKey × Cipher → SPTree.Timed Bool) (ACost : PKey × EKey × Cipher → ℕ)
    (c : Cipher) (kgen : SPTree.Timed (PKey × SKey)) (encap : PKey → SPTree.Timed (Key × EKey))
    (encapCost : PKey → ℕ) {T a tk tE te : ℕ} (hA : ∀ x, (A x).time ≤ T)
    (hAc : ∀ x, ACost x ≤ a) (hk : kgen.time ≤ tk) (hE : ∀ pk, (encap pk).time ≤ tE)
    (he : ∀ pk, encapCost pk ≤ te) :
    SPTree.Timed.stepTime (ReductionDEM.tree.timed KEM A ACost c kgen encap encapCost) ≤
      tk + tE + te + T + a + 2 := by
  time_bound

/-- **Time of the second KEM hop.** A distinguisher `A` of time at most `T` and call cost at
most `a`, with a DEM encryption of cost at most `te`, gives a reduction of time at most
`T + a + te + 2`. -/
theorem ReductionKEM2.tree.timeBound_timed {PKey Key EKey Plain Cipher : Type}
    (DEM : DEMScheme Key Plain Cipher) (nullPlain : Plain)
    (A : PKey × EKey × Cipher → SPTree.Timed Bool) (ACost : PKey × EKey × Cipher → ℕ)
    (enc : Key → Plain → Cipher) (encCost : Key → Plain → ℕ) {T a te : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a) (he : ∀ k p, encCost k p ≤ te)
    (c : PKey × EKey × Key) :
    SPTree.Timed.stepTime (ReductionKEM2.tree.timed DEM nullPlain A ACost c enc encCost) ≤
      T + a + te + 2 := by
  time_bound

end CatCrypt.Examples.KEMDEM
