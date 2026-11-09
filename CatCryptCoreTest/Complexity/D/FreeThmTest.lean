/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.GenericGroup
import CatCryptCore.Complexity.D.FreeThm

/-!
# The command `free_theorem`: tests

Each generated theorem is checked against the statement of the instance it regenerates, by an
`example` with that statement proved by the generated theorem.

* Non-interference: the term `niT` of the tests of `resp_b`, the statement of its instance of
  `Tm.free_noninterference`; a definition reflected by `reflect_d`.
* Commutation with a homomorphism: square-and-multiply, the statement of
  `GenericGroup.powT_commute`; the cube `x · (x · x)`, the statement of
  `GenericGroup.hom_commute`; with the equality test, a term over `isoCtx`, the statement of
  `GenericGroup.iso_commute`.
* Non-interference with several secret variables: two secret words in front of a public `ℕ`,
  secret words around a public `ℕ`, and a secret word in front of an environment of operations
  related by the relation of the secret types (`noninterference_ops`).
* Representation independence: the polynomial `x * x + 1` over field operations in an
  environment related to another by the graph of an encoding, the statement of
  `rep_independence_input` of the development's `Bridges/Transfer/RepIndependence` with the two
  environments of operations as parameters; the same term with the input in the environment.
* A branch on a secret boolean is refused.
-/

set_option autoImplicit false
set_option linter.privateModule false

namespace CatCrypt.Complexity.D.FreeThmTest

open CatCrypt.Complexity.D GenericGroup

/-! ## Non-interference -/

/-- A term over a secret word and a public `ℕ`: the public value plus one when it is zero, else
two. -/
def niT : Tm (.base (.word 64) :: [.nat]) .nat :=
  .ite (.prim .natEq (.pair (.var (.there .here)) (.natLit 0)))
    (.prim .natAdd (.pair (.var (.there .here)) (.natLit 1))) (.natLit 2)

free_theorem niT_free {Sec : FTy → Prop} (hs : Sec (.word 64)) (hb : ¬ Sec .bool)
  for niT at noninterference hs

example {Sec : FTy → Prop} (hs : Sec (.word 64)) (hb : ¬ Sec .bool) (ρ : Env [.nat])
    (k k' : (FTy.word 64).den) :
    (niT.eval (ρ.cons (τ := .base (.word 64)) k)).cost =
        (niT.eval (ρ.cons (τ := .base (.word 64)) k')).cost ∧
      (Ty.nat.Pub Sec →
        niT.eval (ρ.cons (τ := .base (.word 64)) k) =
          niT.eval (ρ.cons (τ := .base (.word 64)) k')) :=
  niT_free hs hb ρ k k'

/-- A Lean definition with a secret word as its last parameter, which it does not use. -/
def addOne (n : ℕ) (k : BitVec 64) : ℕ := (fun _ => n + 1) k

free_theorem addOne_ni {Sec : FTy → Prop} (hs : Sec (.word 64))
  for reflect_d addOne at noninterference hs using [Ty.Pub.nat]

example {Sec : FTy → Prop} (hs : Sec (.word 64)) (ρ : Env [.nat]) (k k' : (FTy.word 64).den) :
    (addOne.d.eval (ρ.cons (τ := .base (.word 64)) k)).cost =
        (addOne.d.eval (ρ.cons (τ := .base (.word 64)) k')).cost ∧
      (Ty.nat.Pub Sec →
        addOne.d.eval (ρ.cons (τ := .base (.word 64)) k) =
          addOne.d.eval (ρ.cons (τ := .base (.word 64)) k')) :=
  addOne_ni hs ρ k k'

/-! ## Non-interference with several secret variables -/

/-- A term over two secret words and a public `ℕ`: the public value plus one. -/
def ni2T : Tm [.base (.word 64), .base (.word 64), .nat] .nat :=
  .prim .natAdd (.pair (.var (.there (.there .here))) (.natLit 1))

free_theorem ni2T_ni {Sec : FTy → Prop} (hs : Sec (.word 64))
  for ni2T at noninterference hs hs

example {Sec : FTy → Prop} (hs : Sec (.word 64)) (ρ : Env [.nat])
    (k1 k1' k2 k2' : (FTy.word 64).den) :
    (ni2T.eval (Env.cons (τ := .base (.word 64)) k1
        (Env.cons (τ := .base (.word 64)) k2 ρ))).cost =
      (ni2T.eval (Env.cons (τ := .base (.word 64)) k1'
        (Env.cons (τ := .base (.word 64)) k2' ρ))).cost ∧
      (Ty.nat.Pub Sec →
        ni2T.eval (Env.cons (τ := .base (.word 64)) k1
            (Env.cons (τ := .base (.word 64)) k2 ρ)) =
          ni2T.eval (Env.cons (τ := .base (.word 64)) k1'
            (Env.cons (τ := .base (.word 64)) k2' ρ))) :=
  ni2T_ni hs ρ k1 k1' k2 k2'

/-- A term over a secret word, a public `ℕ` and a secret word: the public value plus one. -/
def ni3T : Tm [.base (.word 64), .nat, .base (.word 64)] .nat :=
  .prim .natAdd (.pair (.var (.there .here)) (.natLit 1))

free_theorem ni3T_ni {Sec : FTy → Prop} (hs : Sec (.word 64))
  for ni3T at noninterference hs _ hs

example {Sec : FTy → Prop} (hs : Sec (.word 64)) (k1 k1' : (FTy.word 64).den) (p2 : ℕ)
    (k3 k3' : (FTy.word 64).den) :
    (ni3T.eval (Env.cons (τ := .base (.word 64)) k1 (Env.cons (τ := .nat) p2
        (Env.cons (τ := .base (.word 64)) k3 Env.nil)))).cost =
      (ni3T.eval (Env.cons (τ := .base (.word 64)) k1' (Env.cons (τ := .nat) p2
        (Env.cons (τ := .base (.word 64)) k3' Env.nil)))).cost ∧
      (Ty.nat.Pub Sec →
        ni3T.eval (Env.cons (τ := .base (.word 64)) k1 (Env.cons (τ := .nat) p2
            (Env.cons (τ := .base (.word 64)) k3 Env.nil))) =
          ni3T.eval (Env.cons (τ := .base (.word 64)) k1' (Env.cons (τ := .nat) p2
            (Env.cons (τ := .base (.word 64)) k3' Env.nil)))) :=
  ni3T_ni hs k1 k1' p2 k3 k3'

/-- A binary operation applied to a secret word twice. -/
def opsT : Tm [.base (.word 64), .arr (.prod (.base (.word 64)) (.base (.word 64)))
    (.base (.word 64))] (.base (.word 64)) :=
  .app (.var (.there .here)) (.pair (.var .here) (.var .here))

free_theorem opsT_ni {Sec : FTy → Prop} (hs : Sec (.word 64))
  {ρ δ : Env [.arr (.prod (.base (.word 64)) (.base (.word 64))) (.base (.word 64))]}
  (h : EnvRelB (BRel.secret Sec) ρ δ) for opsT at noninterference_ops h hs

example {Sec : FTy → Prop} (hs : Sec (.word 64))
    {ρ δ : Env [.arr (.prod (.base (.word 64)) (.base (.word 64))) (.base (.word 64))]}
    (h : EnvRelB (BRel.secret Sec) ρ δ) (k1 k1' : (FTy.word 64).den) :
    (opsT.eval (Env.cons (τ := .base (.word 64)) k1 ρ)).cost =
        (opsT.eval (Env.cons (τ := .base (.word 64)) k1' δ)).cost ∧
      (Ty.Pub Sec (.base (.word 64)) →
        opsT.eval (Env.cons (τ := .base (.word 64)) k1 ρ) =
          opsT.eval (Env.cons (τ := .base (.word 64)) k1' δ)) :=
  opsT_ni hs h k1 k1'

/-! ## Commutation with a homomorphism -/

free_theorem powT_free {g : FTy} {φ : g.den → g.den} {M N : GrpOps g.den}
  (hφ : M.IsHom N φ) (hg : FTy.bool ≠ g) for powT g at hom_commute hφ

example {g : FTy} {φ : g.den → g.den} {M N : GrpOps g.den} (hφ : M.IsHom N φ)
    (hg : FTy.bool ≠ g) (c : OpCost) (x : g.den) (bits : List Bool) :
    CTree.Lift (fun a b => φ a = b) ((powT g).eval (powEnv g M c x bits))
        ((powT g).eval (powEnv g N c (φ x) bits)) ∧
      ((powT g).eval (powEnv g M c x bits)).cost =
        ((powT g).eval (powEnv g N c (φ x) bits)).cost :=
  powT_free hφ hg c x bits

/-- The cube `x · (x · x)` over the group operations. -/
def cubeT (g : FTy) : Tm (.base g :: homCtx g) (.base g) :=
  .app (.var (.there .here)) (.pair (.var .here)
    (.app (.var (.there .here)) (.pair (.var .here) (.var .here))))

free_theorem cubeT_commute {g : FTy} {φ : g.den → g.den} {M N : GrpOps g.den}
  (hφ : M.IsHom N φ) for cubeT g at hom_commute hφ

example {g : FTy} {φ : g.den → g.den} {M N : GrpOps g.den} (hφ : M.IsHom N φ) (c : OpCost)
    (x : g.den) :
    CTree.Lift (fun a b => φ a = b) ((cubeT g).eval (homEnv₁ g M c x))
        ((cubeT g).eval (homEnv₁ g N c (φ x))) ∧
      ((cubeT g).eval (homEnv₁ g M c x)).cost = ((cubeT g).eval (homEnv₁ g N c (φ x))).cost :=
  cubeT_commute hφ c x

/-- The element `x` if `x = x · x`, else `x · x`, over the group operations and the equality
test. -/
def idemT (g : FTy) : Tm (.base g :: isoCtx g) (.base g) :=
  .ite (.app (.var (.there .here))
      (.pair (.var .here) (.app (.var (.there (.there .here))) (.pair (.var .here) (.var .here)))))
    (.var .here) (.app (.var (.there (.there .here))) (.pair (.var .here) (.var .here)))

free_theorem idemT_commute {g : FTy} {φ : g.den → g.den} {M N : GrpOps g.den}
  (hφ : M.IsHom N φ) (hinj : Function.Injective φ) (hg : FTy.bool ≠ g)
  for idemT g at iso_commute hφ hinj hg

example {g : FTy} {φ : g.den → g.den} {M N : GrpOps g.den} (hφ : M.IsHom N φ)
    (hinj : Function.Injective φ) (hg : FTy.bool ≠ g) (c : OpCost) (x : g.den) :
    CTree.Lift (fun a b => φ a = b) ((idemT g).eval (isoEnv₁ g M c x))
        ((idemT g).eval (isoEnv₁ g N c (φ x))) ∧
      ((idemT g).eval (isoEnv₁ g M c x)).cost = ((idemT g).eval (isoEnv₁ g N c (φ x))).cost :=
  idemT_commute hφ hinj hg c x

/-! ## Representation independence -/

/-- The context of field operations: multiplication, addition, zero and one, innermost first. -/
abbrev opsCtx (g : FTy) : List Ty :=
  [.arr (.prod (.base g) (.base g)) (.base g), .arr (.prod (.base g) (.base g)) (.base g),
    .base g, .base g]

/-- The polynomial `x * x + 1` over the field operations, with input `x`. -/
def sqPlusOne (g : FTy) : Tm (.base g :: opsCtx g) (.base g) :=
  .app (.var (.there (.there .here)))
    (.pair (.app (.var (.there .here)) (.pair (.var .here) (.var .here)))
      (.var (.there (.there (.there (.there .here))))))

free_theorem sqPlusOne_rep {g : FTy} {φ : g.den → g.den} {ρ δ : Env (opsCtx g)}
  (h : EnvRelB (homRel g φ) ρ δ) for sqPlusOne g at rep_independence h

example {g : FTy} {φ : g.den → g.den} {ρ δ : Env (opsCtx g)} (h : EnvRelB (homRel g φ) ρ δ)
    (x : g.den) :
    CTree.Lift (fun a b => φ a = b) ((sqPlusOne g).eval (ρ.cons x))
        ((sqPlusOne g).eval (δ.cons (φ x))) ∧
      ((sqPlusOne g).eval (ρ.cons x)).cost = ((sqPlusOne g).eval (δ.cons (φ x))).cost :=
  sqPlusOne_rep h x

free_theorem sqPlusOne_rep_env {g : FTy} {φ : g.den → g.den}
  {ρ δ : Env (.base g :: opsCtx g)} (h : EnvRelB (homRel g φ) ρ δ)
  for sqPlusOne g at rep_independence h

example {g : FTy} {φ : g.den → g.den} {ρ δ : Env (.base g :: opsCtx g)}
    (h : EnvRelB (homRel g φ) ρ δ) :
    CTree.Lift (fun a b => φ a = b) ((sqPlusOne g).eval ρ) ((sqPlusOne g).eval δ) ∧
      ((sqPlusOne g).eval ρ).cost = ((sqPlusOne g).eval δ).cost :=
  sqPlusOne_rep_env h

/-! ## Refusal -/

/-- A branch on a boolean variable in front of a secret word. -/
def branchT : Tm [.base (.word 64), .base .bool] .nat :=
  .ite (.var (.there .here)) (.natLit 0) (.natLit 1)

/--
error: resp_b: no registered lemma closes the obligation
  ∀ (b b' : FTy.bool.den), BRel.secret Sec FTy.bool b b' → b = b'
-/
#guard_msgs in
free_theorem branchT_ni {Sec : FTy → Prop} (hs : Sec (.word 64)) (hb : Sec .bool)
  for branchT at noninterference hs

end CatCrypt.Complexity.D.FreeThmTest
