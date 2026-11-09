/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.GenericGroup
import CatCryptCore.Complexity.D.RespB

/-!
# The tactic `resp_b`: tests

* Square-and-multiply respects the graph of a map of a group other than `bool`: the statement of
  `GenericGroup.powT_respB`, by `resp_b` with the lemmas of `homRel` registered.
* Non-interference (`Tm.free_noninterference`): a term with a secret word variable in front of a
  public `ℕ` that branches on a comparison of the public value and adds to it respects the
  relation of the secret types, by `resp_b` with `Prim.respB_of_pub`, `BRel.secret_eq` and the
  constructors of `Ty.Pub` registered; the free theorem then gives equal cost and equal trees.
* Under the identity extension hypothesis `∀ f a b, R f a b ↔ a = b` the seeded registry alone
  proves respect.
* A term that uses only the variables of its context respects every base relation.
* A branch on a secret boolean is refused.
-/

set_option autoImplicit false
set_option linter.privateModule false

namespace CatCrypt.Complexity.D

attribute [resp_b] GenericGroup.homRel_of_ne GenericGroup.homRel_self
attribute [resp_b] BRel.secret_eq Prim.respB_of_pub
attribute [resp_b] Ty.Pub.base Ty.Pub.nat Ty.Pub.prod Ty.Pub.sum Ty.Pub.list

/-! ## Generic group: square-and-multiply -/

open GenericGroup in
example {g : FTy} {φ : g.den → g.den} (hg : FTy.bool ≠ g) : (powT g).RespB (homRel g φ) := by
  resp_b

/-! ## Non-interference -/

/-- A term over a secret word and a public `ℕ`: the public value plus one when it is zero, else
two. -/
def niT : Tm (.base (.word 64) :: [.nat]) .nat :=
  .ite (.prim .natEq (.pair (.var (.there .here)) (.natLit 0)))
    (.prim .natAdd (.pair (.var (.there .here)) (.natLit 1))) (.natLit 2)

example {Sec : FTy → Prop} (hb : ¬ Sec .bool) : niT.RespB (BRel.secret Sec) := by
  resp_b

example {Sec : FTy → Prop} (hs : Sec (.word 64)) (hb : ¬ Sec .bool) (ρ : Env [.nat])
    (k k' : (FTy.word 64).den) :
    (niT.eval (ρ.cons (τ := .base (.word 64)) k)).cost =
        (niT.eval (ρ.cons (τ := .base (.word 64)) k')).cost ∧
      (Ty.nat.Pub Sec →
        niT.eval (ρ.cons (τ := .base (.word 64)) k) =
          niT.eval (ρ.cons (τ := .base (.word 64)) k')) :=
  Tm.free_noninterference hs niT (by resp_b) (by simp [Ty.Pub.nat]) ρ k k'

/-! ## Identity extension -/

example {R : BRel} (hR : ∀ f a b, R f a b ↔ a = b) : niT.RespB R := by
  resp_b

/-! ## A term of variables only -/

/-- The application of the first variable to the pair of the second with itself. -/
def appT (g : FTy) : Tm (.arr (.prod (.base g) (.base g)) (.base g) :: [.base g]) (.base g) :=
  .app (.var .here) (.pair (.var (.there .here)) (.var (.there .here)))

example (g : FTy) (R : BRel) : (appT g).RespB R := by
  resp_b

/-! ## Refusal -/

/-- A branch on a boolean variable. -/
def branchT : Tm [.base .bool] .nat := .ite (.var .here) (.natLit 0) (.natLit 1)

/--
error: resp_b: no registered lemma closes the obligation
  ∀ (b b' : FTy.bool.den), BRel.secret Sec FTy.bool b b' → b = b'
-/
#guard_msgs in
example {Sec : FTy → Prop} (hb : Sec .bool) : branchT.RespB (BRel.secret Sec) := by
  resp_b

end CatCrypt.Complexity.D
