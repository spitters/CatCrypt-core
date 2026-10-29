/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.DeriveCost

/-!
# Tests for the field rules of `derive_cost` and `derive_timed`

* `Ex.eval` and `Ex.evalList`: evaluation of expressions over a local language `L : LLang`, a
  mutual structural recursion over a nested inductive type whose bodies apply the field
  `L.eval` and the environment `ρ`. `derive_cost Ex.eval` defines both costs, which take
  the cost companion of `ρ` after `ρ` and the cost companion of `L.eval` after their binders.
* `Ex.evalTwice`: a caller of the block outside it, which passes its companion of `L.eval`.
* `evalRed`: an oracle tree calling `Ex.eval`; its costed form takes the companion of
  `L.eval`.
* `countLeaks`: a recursion whose cost takes the companion of the field `w.leaks` of its
  corruption binder `w : Corr`. `leakRed` passes the corruption as a constructor application
  and `leakLetRed` binds it by a `let`; in both, the companion of `leaks` is the cost of the
  function the structure holds.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveCostFieldTest

open CatCrypt.Crypto

/-- A local language: values, operators and their evaluation. -/
structure LLang where
  /-- Values. -/
  Val : Type
  /-- Operators. -/
  Op : Type
  /-- Evaluation of an operator on its arguments. -/
  eval : Op → List Val → Option Val

/-- Expressions over a local language. -/
inductive Ex (L : LLang) where
  | var (x : ℕ)
  | lit (v : L.Val)
  | op (o : L.Op) (args : List (Ex L))

mutual
/-- Evaluation of an expression. -/
def Ex.eval {L : LLang} (ρ : ℕ → Option L.Val) : Ex L → Option L.Val
  | .var x => ρ x
  | .lit v => some v
  | .op o args => (Ex.evalList ρ args).bind (L.eval o)
/-- Evaluation of a list of expressions. -/
def Ex.evalList {L : LLang} (ρ : ℕ → Option L.Val) : List (Ex L) → Option (List L.Val)
  | [] => some []
  | e :: es => (Ex.eval ρ e).bind fun v => (Ex.evalList ρ es).map (v :: ·)
end

derive_cost Ex.eval

/-- Two evaluations of an expression. -/
def Ex.evalTwice {L : LLang} (ρ : ℕ → Option L.Val) (e : Ex L) :
    Option L.Val × Option L.Val :=
  (Ex.eval ρ e, Ex.eval ρ e)

derive_cost Ex.evalTwice

/-- An oracle tree returning the value of an expression. -/
def evalRed {D R : Type} {L : LLang} (ρ : ℕ → Option L.Val) (e : Ex L) :
    OracleAdv D R (Option L.Val) :=
  .ret (Ex.eval ρ e)

derive_timed evalRed

/-- Corruption parameters. -/
structure Corr where
  /-- The party leaks its values. -/
  leaks : ℕ → Bool
  /-- The value is public. -/
  pub : ℕ → Bool

/-- The number of leaking parties of a list. -/
def countLeaks (w : Corr) : List ℕ → ℕ
  | [] => 0
  | p :: ps => (if w.leaks p then 1 else 0) + countLeaks w ps

/-- The corruption passed as a constructor application. -/
def leakRed {D R : Type} (f g : ℕ → Bool) (ps : List ℕ) : OracleAdv D R ℕ :=
  .ret (countLeaks ⟨f, g⟩ ps)

derive_timed leakRed

/-- The corruption bound by a `let`. -/
def leakLetRed {D R : Type} (f g : ℕ → Bool) (ps : List ℕ) : OracleAdv D R ℕ :=
  let w : Corr := ⟨f, g⟩
  .ret (countLeaks w ps)

derive_timed leakLetRed

end CatCrypt.Tactics.DeriveCostFieldTest
