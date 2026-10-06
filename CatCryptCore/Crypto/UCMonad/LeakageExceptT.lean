/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Std.Do.Triple
public import Std.Tactic.Do
public import Mathlib.Control.EquivFunctor


@[expose] public section
set_option autoImplicit false

/-!
# Leakage is the `.except` / `ExceptT` branch — tier 1 of leakage internalization

A leakage channel is modeled as an output the environment observes but the honest
protocol does not consume: a computation `T (b ⊕ I)` returning either a normal
result `b` (`.inl`) or a *leaked* value `I` (`.inr`). This module machine-checks
two claims about that channel.

**(a) Leakage output = the exception branch.** `T (b ⊕ I) ≃ ExceptT I T b`, the
iso `leakEquiv`. Since `ExceptT I T b` unfolds to `T (Except I b)` and
`b ⊕ I ≃ Except I b` (the leaked `.inr i` is exactly the exception `.error i`),
the channel iso is the lawful-functor image `EquivFunctor.mapEquiv T` of the
pointwise sum↔except iso `sumExceptEquiv`. The crux `sumExceptEquiv_inr`
(`Sum.inr i ↦ Except.error i`) is the sentence "the leaked value *is* the
exception".

**(d) mvcgen walks the leakage branch natively.** A concrete leaky program
`leakyProg : Nat → ExceptT String (StateM Nat) Nat` records its argument into the
transcript state and then either leaks (`throw`, the `.except` barrel) or returns
a normal result (`pure`, the success barrel). `leakyProg_spec` is a `Std.Do`
Hoare triple whose postcondition constrains **both** barrels — the `⇓` success
value and the exception/leakage value — and `mvcgen` fires on it directly,
reducing along the upstream `.except`-shape `@[spec]` lemmas (`Spec.throw_ExceptT`,
`Spec.pure`, the lifted `set`) with **no new machinery**: the `.except I` leakage
branch is discharged by the same weakest-precondition metatheory that walks the
success branch.

Together: leakage internalizes as `ExceptT`'s exception layer, and the program
logic that already ships for `ExceptT` reasons about it for free —
`T (b ⊕ I) ≅ ExceptT I T b`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Std.Do

universe u v

/-! ## 1. (a) The pointwise leakage↔exception iso

`b ⊕ I ≃ Except I b`: a normal result `.inl v` is the success value `.ok v`; a
leaked value `.inr i` is the exception value `.error i`. -/

/-- **The leakage↔exception iso, pointwise.** A normal result (`Sum.inl`) is the
    `Except` success value; a leaked value (`Sum.inr`) is the `Except` exception
    value. This is the value-level statement "leakage = the exception branch". -/
def sumExceptEquiv {b I : Type u} : b ⊕ I ≃ Except I b where
  toFun x := match x with | .inl v => .ok v | .inr e => .error e
  invFun x := match x with | .ok v => .inl v | .error e => .inr e
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

/-- **The crux of (a): a leaked value is an exception.** The `.inr i` leakage
    output maps to the `.error i` exception value. -/
@[simp] theorem sumExceptEquiv_inr {b I : Type u} (i : I) :
    (sumExceptEquiv (b := b) (I := I)) (Sum.inr i) = Except.error i := rfl

/-- A normal result maps to the `Except` success value. -/
@[simp] theorem sumExceptEquiv_inl {b I : Type u} (v : b) :
    (sumExceptEquiv (b := b) (I := I)) (Sum.inl v) = Except.ok v := rfl

/-! ## 2. (a) The channel iso `T (b ⊕ I) ≃ ExceptT I T b`

Applying `sumExceptEquiv` under a lawful monad `T` (via `EquivFunctor.mapEquiv`)
turns the leakage channel `T (b ⊕ I)` into `T (Except I b) = ExceptT I T b`. -/

/-- **(a) Leakage output = the `ExceptT` exception branch.** For any lawful monad
    `T`, the leakage channel `T (b ⊕ I)` is isomorphic to `ExceptT I T b`: map the
    pointwise `sumExceptEquiv` under `T`. The target type `ExceptT I T b` unfolds
    definitionally to `T (Except I b)`, so this is `EquivFunctor.mapEquiv T`
    applied to the value-level leak↔exception iso. -/
def leakEquiv (T : Type u → Type v) [Monad T] [LawfulMonad T] (b I : Type u) :
    T (b ⊕ I) ≃ ExceptT I T b :=
  EquivFunctor.mapEquiv T sumExceptEquiv

/-- **The channel iso is the functorial image of the value iso.** `leakEquiv`
    acts by mapping `sumExceptEquiv` over the outputs of `T`: a `T`-computation
    whose value is a normal-or-leaked sum becomes the `T`-computation whose value
    is the corresponding success-or-exception `Except`. -/
theorem leakEquiv_apply (T : Type u → Type v) [Monad T] [LawfulMonad T]
    (b I : Type u) (x : T (b ⊕ I)) :
    leakEquiv T b I x = sumExceptEquiv <$> x := rfl

/-! ## 3. (d) A concrete leaky program in `ExceptT I (StateM S)`

`leakyProg` writes its argument into the transcript state, then either leaks
(`throw`, the exception/`.except` barrel) or returns a doubled result (`pure`,
the success barrel). This is a leakage channel realized *as* `ExceptT`. -/

/-- **A leaky program.** Records `secret` into the transcript state (`set`), then
    on `secret = 0` leaks the marker string `"leaked-zero"` on the exception
    branch, otherwise returns the normal result `secret * 2` on the success
    branch. The `.except String` layer is the leakage channel. -/
def leakyProg (secret : Nat) : ExceptT String (StateM Nat) Nat := do
  set secret
  if secret = 0 then
    throw "leaked-zero"
  else
    pure (secret * 2)

/-- **(d) `mvcgen` discharges a triple over `ExceptT` natively, walking the
    leakage branch.** The postcondition constrains **both** barrels: the `⇓`
    success value (normal result `secret * 2`, transcript `secret`, `secret ≠ 0`)
    and the leakage/exception value (`"leaked-zero"`, transcript `secret = 0`).
    `mvcgen` fires directly — the lifted `set`, the `if`, `throw` (`.except`) and
    `pure` (success) all reduce along the upstream `.except`-shape `@[spec]`
    lemmas, and `mvcgen` closes the residual arithmetic/string VCs itself. No new
    machinery is introduced for the `.except` leakage barrel; it is walked exactly
    like the success barrel. -/
theorem leakyProg_spec (secret : Nat) :
    ⦃fun _ => ⌜True⌝⦄
    (leakyProg secret)
    ⦃post⟨fun r s => ⌜r = secret * 2 ∧ s = secret ∧ secret ≠ 0⌝,
          fun leak s => ⌜leak = "leaked-zero" ∧ s = secret ∧ secret = 0⌝⟩⦄ := by
  mvcgen [leakyProg]

end CatCrypt.Crypto.SecureCompilation.Ascent
