/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.CwFPi

/-!
# Tests of the category with families of containers

The identity function of the polynomial model, whose partial backward map returns each result
position to the argument, and a projection lens that is non-interfering for the secret component,
through equation (9) of Moss and von Glehn at pairs of runs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Container.CwF.Test

open PFunctor

/-- A context with shapes `ℕ` and positions `Bool`. -/
abbrev Γ₀ : Ctx.{0} := ⟨ℕ, fun _ => Bool⟩

/-- A type with shapes `ℕ` and positions `Bool`. -/
def natTy : Ty Γ₀ := ⟨fun _ => ℕ, fun _ _ => Bool⟩

/-- The identity function of a type. -/
def idFun {Γ : Ctx.{0}} (A : Ty Γ) : Tm Γ (Ty.pi A (A.sub (wk A))) := Tm.lam (var A)

example (γ a : ℕ) : ((idFun natTy).S γ).fwd a = a := rfl

example (γ a : ℕ) (b : Bool) : ((idFun natTy).S γ).back a b = some b := rfl

example : Tm.app (idFun natTy) = var natTy := Tm.app_lam _

/-- A pair of a public and a secret component, whose position `false` reads the public one. -/
abbrev pairCont : PFunctor.{0, 0} := ⟨ℕ × ℕ, fun _ => Bool⟩

/-- The output container: one position. -/
abbrev outCont : PFunctor.{0, 0} := ⟨ℕ, fun _ => PUnit⟩

/-- Agreement of two pairs at a component. -/
def pairAgree : Agree pairCont := fun a a' b => cond b (a.2 = a'.2) (a.1 = a'.1)

/-- Agreement of two outputs. -/
def outAgree : Agree outCont := fun n n' _ => n = n'

/-- The projection to the public component, demanding the position `false`. -/
def pubLens : Lens pairCont outCont := ⟨Prod.fst, fun _ _ => false⟩

example : DepSound pairAgree outAgree pubLens := fun _ _ _ h => h

example :
    DNSound pairAgree.toPred outAgree.toPred (runPairLens (DNLens.ofLens pubLens)) :=
  dnSound_runPair_iff.2 (agreeSound_ofLens_iff.2 fun _ _ _ h => h)

end CatCrypt.Container.CwF.Test
