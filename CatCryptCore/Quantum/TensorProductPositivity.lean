/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.Tactic.PositivityMatrix
public import CatCryptCore.Quantum.KronNf
public import CatCryptCore.Quantum.TensorProduct
public meta import Lean.Elab.Tactic

/-!
# `positivity` extension for the `Fin`-indexed Kronecker product

`CatCrypt.Quantum.TensorProduct.kronecker A B` is Mathlib's `A ⊗ₖ B` reindexed along
`finProdFinEquiv` (`kronecker_eq_reindex`). The extension below makes `positivity` and `psd`
prove `0 ≤ kronecker A B` and `(kronecker A B).PosSemidef` from positivity of the factors.

## Main results

* `CatCrypt.Quantum.TensorProduct.posSemidef_kronecker`: the product of positive semidefinite
  matrices is positive semidefinite.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.TensorProduct

open scoped ComplexOrder

variable {d₁ d₂ : ℕ}

/-- The `Fin`-indexed Kronecker product of positive semidefinite matrices is positive
semidefinite. -/
theorem posSemidef_kronecker {A : Matrix (Fin d₁) (Fin d₁) ℂ} {B : Matrix (Fin d₂) (Fin d₂) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (kronecker A B).PosSemidef := by
  rw [kronecker_eq_reindex]
  exact (hA.kronecker hB).reindex _

end CatCrypt.Quantum.TensorProduct

end

public meta section

namespace CatCryptCore.Tactic.PositivityMatrix

open Lean Meta Elab Tactic Qq Mathlib.Meta.Positivity

/-- The `positivity` extension for the `Fin`-indexed Kronecker product `kronecker a b`. -/
@[positivity CatCrypt.Quantum.TensorProduct.kronecker _ _]
def evalTensorKronecker : PositivityExt where eval {_u α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => do
    let some _ ← matSquare? α | return .none
    let e' := e.consumeMData
    unless e'.isAppOfArity ``CatCrypt.Quantum.TensorProduct.kronecker 4 do return .none
    let some ha ← psdOf e'.appFn!.appArg! | return .none
    let some hb ← psdOf e'.appArg! | return .none
    ofPSD zα pα e (← mkAppM ``CatCrypt.Quantum.TensorProduct.posSemidef_kronecker #[ha, hb])

end CatCryptCore.Tactic.PositivityMatrix

end
