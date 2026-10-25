/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.DeriveCost
public import CatCryptCore.Tactics.StdCosts

/-!
# Tests of fields of computed structures and of union, image and filter costs

* the registered costs of `Multiset.ndunion`, `Finset.image` and `Finset.filter` of
  `CatCryptCore.Tactics.StdCosts` (`unionM`, `imgF`, `filtF`);
* a callee cost taking the companion of a field of a structure computed by a definition
  `Corr.ofAttack P A`, passed directly (`redC`) or bound by a `let` in an unfolded data function
  (`redL`): the companion is indexed by `P` and `A`; passed to a callee with a costed form
  (`redM`), the field keeps the companion of the path at the call, as before.

## Main results

* `redC.erase_timed`, `redL.erase_timed`, `redM.erase_timed`, emitted by `derive_timed`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedComputedFieldTest

open CatCrypt.Crypto

/-- A union of multisets. -/
def unionM (s t : Multiset ℕ) : Multiset ℕ := s.ndunion t

/-- An image of a finite set. -/
def imgF (s : Finset ℕ) : Finset ℕ := s.image (· + 1)

/-- A filter of a finite set. -/
def filtF (s : Finset ℕ) : Finset ℕ := s.filter (· < 3)

derive_cost unionM
derive_cost imgF
derive_cost filtF

example (s t : Multiset ℕ) : unionM.timedCost s t = 1 + Multiset.ndunion.timedCost ℕ s t := rfl

example (s : Finset ℕ) :
    imgF.timedCost s = 1 + Finset.image.timedCost ℕ ℕ (· + 1) (fun _ => 1) s := rfl

example (s : Finset ℕ) : filtF.timedCost s = 1 + Finset.filter.timedCost ℕ (· < 3) s := rfl

/-- A corruption structure with two function fields. -/
structure Corr where
  /-- Whether a party leaks. -/
  leaks : ℕ → Bool
  /-- Whether a label is public. -/
  pub : ℕ → Bool

/-- The corruption of a static attack, computed by a definition. -/
def Corr.ofAttack (P : ℕ → ℕ) (A : List ℕ) : Corr where
  leaks p := decide (P p ∈ A)
  pub l := decide (l ∈ A)

/-- A step reading the field `pub` of a corruption. -/
def stepC (w : Corr) (n : ℕ) : Bool := w.pub n

derive_cost stepC

/-- A reduction calling `stepC` at a computed corruption. -/
def redC {D R : Type} (P : ℕ → ℕ) (A : List ℕ) (n : ℕ) : OracleAdv D R Bool :=
  .ret (stepC (Corr.ofAttack P A) n)

derive_timed redC

/-- The costed form of `redC` takes the companion of `pub` at `Corr.ofAttack P A`, indexed by
`P` and `A`, after its binders. -/
example {D R : Type} (P PCost : ℕ → ℕ) (A : List ℕ) (n : ℕ)
    (ofAttack_pubCost : (ℕ → ℕ) → List ℕ → ℕ → ℕ) :
    ((redC.timed (D := D) (R := R) P PCost A n ofAttack_pubCost).2).erase = redC P A n :=
  redC.erase_timed ..

/-- A data function binding the computed corruption by a `let`. -/
def viaC (P : ℕ → ℕ) (A : List ℕ) (n : ℕ) : Bool :=
  let w := Corr.ofAttack P A
  stepC w n

/-- A reduction calling `viaC`. -/
def redL {D R : Type} (P : ℕ → ℕ) (A : List ℕ) (n : ℕ) : OracleAdv D R Bool :=
  .ret (viaC P A n)

derive_timed redL

example {D R : Type} (P PCost : ℕ → ℕ) (A : List ℕ) (n : ℕ)
    (ofAttack_pubCost : (ℕ → ℕ) → List ℕ → ℕ → ℕ) :
    ((redL.timed (D := D) (R := R) P PCost A n ofAttack_pubCost).2).erase = redL P A n :=
  redL.erase_timed ..

/-- A reduction over a corruption binder. -/
def midC {D R : Type} (w : Corr) (n : ℕ) : OracleAdv D R Bool := .ret (stepC w n)

derive_timed midC

/-- A call of `midC` at a computed corruption. -/
def redM {D R : Type} (P : ℕ → ℕ) (A : List ℕ) (n : ℕ) : OracleAdv D R Bool :=
  midC (Corr.ofAttack P A) n

derive_timed redM

example {D R : Type} (P PCost : ℕ → ℕ) (A : List ℕ) (n : ℕ) (pubCost : ℕ → ℕ) :
    ((redM.timed (D := D) (R := R) P PCost A n pubCost).2).erase = redM P A n :=
  redM.erase_timed ..

end CatCrypt.Tactics.DeriveTimedComputedFieldTest
