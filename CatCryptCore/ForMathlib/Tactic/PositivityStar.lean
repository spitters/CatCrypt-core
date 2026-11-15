/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-!
# `positivity` extensions for star-ordered rings and the continuous functional calculus

The positive cone of a star-ordered ring `R` contains the star squares `star c * c` and
`c * star c`, the squares `a * a` and even powers `a ^ (2 * k)` of self-adjoint elements and the
star projections, and it is closed under the congruences `a ↦ star c * a * c`,
`a ↦ c * a * star c` and, for self-adjoint `c`, `a ↦ c * a * c`. In a C⋆-algebra it also
contains the image of every function that is nonnegative on the spectrum under the continuous
functional calculus, in particular `CFC.sqrt a`, `CFC.abs a`, `a⁺`, `a⁻`, `a ^ (y : ℝ)` and
`a ^ (y : ℝ≥0)`, and the powers `a ^ n` of nonnegative `a`.

The extensions below make `positivity` prove `0 ≤ X` for every term `X` built from these
generators, from atoms with a hypothesis `0 ≤ a`, `IsSelfAdjoint a` or `IsStarProjection a`, and
by the closure rules that Mathlib's `positivity` already has (sums, `Finset.sum`, nonnegative
scalars, `b - a` with `a ≤ b`). A factor is compared with `star c` up to unfolding of
instances.

## Extensions

* `evalStarMul` (`_ * _`): star squares, congruences, squares of self-adjoint elements.
* `evalStarProjection` (any term): `p` and `1 - p` for a star projection `p`.
* `evalCFC`, `evalCFCₙ` (`cfc f a`, `cfcₙ f a`): the hypothesis `∀ x ∈ spectrum R a, 0 ≤ f x`
  is proved by `positivity` on `f x` for a variable `x`.
* `evalCFCSqrt`, `evalCFCAbs`, `evalCFCPosPart`, `evalCFCNegPart`, `evalCFCRpow`,
  `evalCFCNNRpow`: the named functions of the calculus.
* `evalStarPow` (`a ^ n`, `n : ℕ`): even numerals for self-adjoint `a`, and every `n` for
  nonnegative `a` in a C⋆-algebra.

## Main results

* `IsSelfAdjoint.pow_nonneg_of_even`: `0 ≤ a ^ n` for self-adjoint `a` and even `n`.
-/

@[expose] public section

set_option autoImplicit false

/-- In a star-ordered ring an even power of a self-adjoint element is nonnegative. -/
theorem IsSelfAdjoint.pow_nonneg_of_even {R : Type*} [Semiring R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] {a : R} (ha : IsSelfAdjoint a) {n : ℕ} (hn : Even n) : 0 ≤ a ^ n := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_add]
  exact (ha.pow k).mul_self_nonneg

end

public meta section

namespace CatCryptCore.Tactic.PositivityStar

open Lean Meta Qq Mathlib.Meta.Positivity

/-- Whether `x` is `star y` up to unfolding of instances. -/
def isStarOf (x y : Expr) : MetaM Bool := do
  try
    let sy ← mkAppM ``star #[y]
    withTransparency .instances <| isDefEq x sy
  catch _ => pure false

/-- Whether `x` and `y` are the same term up to reducible unfolding. -/
def isSame (x y : Expr) : MetaM Bool := withReducible <| isDefEq x y

/-- The result `0 ≤ e` from the proof `pf`, whose type is checked to be `0 ≤ e` up to unfolding
of instances. -/
def nonnegOf {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (pα : Q(PartialOrder $α))
    (e : Q($α)) (pf : Expr) : MetaM (Strictness zα e (some pα)) := do
  let t ← inferType pf
  unless ← withTransparency .instances <| isDefEq t q(0 ≤ $e) do
    throwError "positivity: the proof of{indentExpr t}\ndoes not prove{indentExpr q(0 ≤ $e)}"
  pure (.nonnegative pf)

/-- A proof of `0 ≤ a` by the core of `positivity`, if it finds one. -/
def coreNonneg {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (pα : Q(PartialOrder $α))
    (a : Q($α)) : MetaM (Option Expr) := do
  match ← catchNone (core zα (some pα) a) with
  | .positive p => pure (some (← mkAppM ``le_of_lt #[p]))
  | .nonnegative p => pure (some p)
  | _ => pure none

/-- A proof of `IsStarProjection x`: a hypothesis, or `x = 1 - p` for such a `p`. -/
partial def starProjOf (x : Expr) : MetaM (Option Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``IsStarProjection 4 then
      if ← isSame t.appArg! x then return some d.toExpr
  let x := x.consumeMData
  if x.isAppOfArity ``HSub.hSub 6 then
    let o := x.appFn!.appArg!
    if o.isAppOfArity ``OfNat.ofNat 3 && o.appFn!.appArg!.rawNatLit? == some 1 then
      if let some hp ← starProjOf x.appArg! then
        return some (← mkAppM ``IsStarProjection.one_sub #[hp])
  return none

/-- Whether the local context has a hypothesis `IsStarProjection p`. -/
def hasStarProjHyp : MetaM Bool := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type).isAppOfArity ``IsStarProjection 4 then return true
  return false

/-- A proof of `IsSelfAdjoint a`: a hypothesis `IsSelfAdjoint a`, a star projection `a`, or
`0 ≤ a` by the core of `positivity` when `core` is set. -/
def selfAdjointOf {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (pα : Q(PartialOrder $α))
    (a : Q($α)) (core : Bool) : MetaM (Option Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``IsSelfAdjoint 3 then
      if ← isSame t.appArg! a then return some d.toExpr
  if let some hp ← starProjOf a then
    return some (← mkAppM ``IsStarProjection.isSelfAdjoint #[hp])
  if core then
    if let some p ← coreNonneg zα pα a then
      return some (← mkAppM ``IsSelfAdjoint.of_nonneg #[p])
  return none

/-- Whether `α` carries `PosMulMono`, so that Mathlib's extensions for products and powers
apply and the recursive cases below are skipped. -/
def hasPosMulMono (α : Expr) : MetaM Bool := do
  try
    let _ ← synthInstance (← mkAppOptM ``PosMulMono #[α, none, none, none])
    pure true
  catch _ => pure false

/-- The `positivity` extension for products in a star-ordered ring: `star c * c`,
`c * star c`, `star c * a * c` and `c * a * star c` with `0 ≤ a`, and, for self-adjoint `c`,
`c * c` and `c * a * c` with `0 ≤ a`. -/
@[positivity _ * _]
def evalStarMul : PositivityExt where eval {_u α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => do
    let .app (.app f x) y := e.consumeMData | throwError "not *"
    unless f.isAppOfArity ``HMul.hMul 4 do throwError "not *"
    let _ ← synthInstance (← mkAppOptM ``StarOrderedRing #[α, none, none, none])
    if ← isStarOf x y then
      return ← nonnegOf zα pα e (← mkAppM ``star_mul_self_nonneg #[y])
    if ← isStarOf y x then
      return ← nonnegOf zα pα e (← mkAppM ``mul_star_self_nonneg #[x])
    let rec_ ← (not <$> hasPosMulMono α)
    if ← isSame x y then
      if let some h ← selfAdjointOf zα pα x rec_ then
        return ← nonnegOf zα pα e (← mkAppM ``IsSelfAdjoint.mul_self_nonneg #[h])
    let .app (.app g c) a := x.consumeMData | return .none
    unless g.isAppOfArity ``HMul.hMul 4 do return .none
    if ← isStarOf c y then
      if let some pa ← coreNonneg zα pα a then
        return ← nonnegOf zα pα e (← mkAppM ``star_left_conjugate_nonneg #[pa, y])
    if ← isStarOf y c then
      if let some pa ← coreNonneg zα pα a then
        return ← nonnegOf zα pα e (← mkAppM ``star_right_conjugate_nonneg #[pa, c])
    if ← isSame c y then
      if let some hc ← selfAdjointOf zα pα c rec_ then
        if let some pa ← coreNonneg zα pα a then
          return ← nonnegOf zα pα e (← mkAppM ``IsSelfAdjoint.conjugate_nonneg #[pa, hc])
    return .none

/-- The `positivity` extension for star projections: `p` and `1 - p` when the local context has
`IsStarProjection p`. -/
@[positivity _]
def evalStarProjection : PositivityExt where eval {_u _α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => do
    unless ← hasStarProjHyp do return .none
    let some hp ← starProjOf e | return .none
    nonnegOf zα pα e (← mkAppM ``IsStarProjection.nonneg #[hp])

/-- A proof of a hypothesis `∀ xs, 0 ≤ t` (or `0 < t`, `t ≠ 0`) of a lemma by `positivity` on
`t` for variables `xs`. -/
def sideByPositivity (t : Expr) : MetaM Expr :=
  forallTelescope t fun xs body => do
    let body ← Core.betaReduce body
    let pf ← Mathlib.Meta.Positivity.solve body
    mkLambdaFVars xs pf

/-- Proves `0 ≤ e` by the lemma `thm` with conclusion `0 ≤ t`: unifies `t` with `e`,
synthesizes the instance arguments left open and proves each remaining hypothesis by
`sideByPositivity`. -/
def applyNonnegLemma {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (pα : Q(PartialOrder $α))
    (e : Q($α)) (thm : Name) : MetaM (Strictness zα e (some pα)) := do
  let c ← mkConstWithFreshMVarLevels thm
  let (xs, bis, ty) ← forallMetaTelescopeReducing (← inferType c)
  let ty := ty.consumeMData
  unless ty.isAppOfArity ``LE.le 4 do throwError "{thm} does not conclude `0 ≤ _`"
  unless ← withTransparency .instances <| isDefEq ty.appArg! e do
    throwError "{thm} does not apply to{indentExpr e}"
  for x in xs, bi in bis do
    let m := x.mvarId!
    if ← m.isAssigned then continue
    let t := (← instantiateMVars (← m.getType)).consumeTypeAnnotations
    if bi.isInstImplicit then
      m.assign (← synthInstance t)
    else if ← isProp t then
      m.assign (← sideByPositivity t)
    else
      throwError "{thm}: argument {x} of type{indentExpr t}\nis not determined"
  nonnegOf zα pα e (← instantiateMVars (mkAppN c xs))

/-- The `positivity` extension for `cfc f a`: `0 ≤ f x` is proved for a variable `x`. -/
@[positivity cfc _ _]
def evalCFC : PositivityExt where eval {_u _α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => applyNonnegLemma zα pα e ``cfc_nonneg

/-- The `positivity` extension for `cfcₙ f a`: `0 ≤ f x` is proved for a variable `x`. -/
@[positivity cfcₙ _ _]
def evalCFCₙ : PositivityExt where eval {_u _α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => applyNonnegLemma zα pα e ``cfcₙ_nonneg

/-- The `positivity` extension for `CFC.sqrt a`. -/
@[positivity CFC.sqrt _]
def evalCFCSqrt : PositivityExt where eval {_u _α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => applyNonnegLemma zα pα e ``CFC.sqrt_nonneg

/-- The `positivity` extension for `CFC.abs a`. -/
@[positivity CFC.abs _]
def evalCFCAbs : PositivityExt where eval {_u _α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => applyNonnegLemma zα pα e ``CFC.abs_nonneg

/-- The `positivity` extension for the positive part `a⁺` of the continuous functional
calculus. -/
@[positivity _⁺]
def evalCFCPosPart : PositivityExt where eval {_u _α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => applyNonnegLemma zα pα e ``CFC.posPart_nonneg

/-- The `positivity` extension for the negative part `a⁻` of the continuous functional
calculus. -/
@[positivity _⁻]
def evalCFCNegPart : PositivityExt where eval {_u _α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => applyNonnegLemma zα pα e ``CFC.negPart_nonneg

/-- The `positivity` extension for the real power `a ^ (y : ℝ)` of the continuous functional
calculus. -/
@[positivity HPow.hPow _ (_ : ℝ)]
def evalCFCRpow : PositivityExt where eval {_u _α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => applyNonnegLemma zα pα e ``CFC.rpow_nonneg

/-- The `positivity` extension for the power `a ^ (y : ℝ≥0)` of the continuous functional
calculus. -/
@[positivity HPow.hPow _ (_ : NNReal)]
def evalCFCNNRpow : PositivityExt where eval {_u _α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => applyNonnegLemma zα pα e ``CFC.nnrpow_nonneg

/-- The `positivity` extension for `a ^ n` with `n : ℕ` in a star-ordered ring: an even numeral
`n` with `a` self-adjoint by a hypothesis, and in a C⋆-algebra every `n` with `0 ≤ a`. -/
@[positivity _ ^ (_ : ℕ)]
def evalStarPow : PositivityExt where eval {_u α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => do
    if ← hasPosMulMono α then return .none
    let e' := e.consumeMData
    unless e'.isAppOfArity ``HPow.hPow 6 do throwError "not ^"
    let a := e'.appFn!.appArg!
    let n := e'.appArg!
    if let some k := n.nat? then
      if k % 2 == 0 then
        if let some ha ← selfAdjointOf zα pα a false then
          let hn ← mkDecideProof (← mkAppM ``Even #[n])
          return ← nonnegOf zα pα e (← mkAppM ``IsSelfAdjoint.pow_nonneg_of_even #[ha, hn])
    applyNonnegLemma zα pα e ``CStarAlgebra.pow_nonneg

end CatCryptCore.Tactic.PositivityStar

end
