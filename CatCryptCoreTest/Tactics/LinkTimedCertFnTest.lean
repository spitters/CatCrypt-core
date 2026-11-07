/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.LinkTimed

/-!
# Tests of certified callees with a function parameter

Fresh definitions, none taken from a protocol. `twice` (a sample, then a function parameter
applied twice) is certified by `derive_timed`, `reflect_d` and `link_timed`; its certificate
`twice.d_timedSim` takes, at the function parameter, the function, its companion, its D value,
the D cost, the step equation and the bound of the D cost by the companion.

* `passF f b := twice f b`: the function parameter of the caller passed through. `reflect_d`
  reflects the call as the closure of `twice.d` (`Reflect.Impl.certFnArg?`), and `link_timed`
  fills the premises of the certificate at the function parameter from the caller's own
  (`LinkTimed.certArgs`): allowance `2`.
* `useNot b := twice (fun x => !x) b`: a λ-term with a pure body at the function parameter;
  `reflect_d` reflects the call as the closure of `twice.d`, the hypothesis at the function
  parameter the derivation of the body at a fresh argument; `link_timed` fills the premises of
  the certificate there from the exact cost judgement of the body (`LinkTimed.closureStep?`) and
  the companion of the closure in the costed tree of the call: allowance `2`.
* `useLet b := twice (fun x => let y := !x; y && x) b`: a closure with a `let`, refused by
  `link_timed`.

## Main definitions

* `twice`, `passF`, `useNot`, `useLet`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.LinkTimedCertFnTest

open CatCrypt.Core CatCrypt.Complexity.D

/-- A coin, then `f` applied twice to it combined with `b`. -/
noncomputable def twice (f : Bool → Bool) (b : Bool) : SPTree Bool :=
  SPTree.sample Bool inferInstance inferInstance fun x => SPTree.ret (f (f (x && b)))

derive_timed twice

reflect_d twice

link_timed twice

/-- The function parameter passed through. -/
noncomputable def passF (f : Bool → Bool) (b : Bool) : SPTree Bool := twice f b

derive_timed passF

reflect_d passF

/-- The call is the closure of the D-term of `twice`, the function bound by `let`. -/
example : passF.d =
    .letE (.var (.there .here)) (.app (.lam (twice.d.rename (Ren.liftN _)))
      (.var (.there .here))) := rfl

link_timed passF

example (f : Bool → Bool) (fCost : Bool → ℕ) (gf : Val (.arr .bool .bool))
    (fDCost : Val .bool → ℕ) (hf : ∀ v, gf v = stepN CTree.tick (fDCost v) (.ret (f v)))
    (hfCost : ∀ v, fDCost v ≤ fCost v) (b : Bool) :
    TimedSim (fun a w => a = w) 1 2 (passF.timed f fCost b)
      (passF.d.eval (Env.cons b (Env.cons gf Env.nil))) :=
  passF.d_timedSim f fCost gf fDCost hf hfCost b

/-- A closure at the function parameter. -/
noncomputable def useNot (b : Bool) : SPTree Bool := twice (fun x => !x) b

derive_timed useNot

reflect_d useNot

/-- The call is the closure of the D-term of `twice`, the closure bound by `let`. -/
example : useNot.d =
    .letE (.lam (.prim .bnot (.var .here))) (.app (.lam (twice.d.rename (Ren.liftN _)))
      (.var (.there .here))) := rfl

link_timed useNot

/-- The certificate of `useNot`: allowance `2`. -/
example (b : Bool) :
    TimedSim (fun a w => a = w) 1 2 (useNot.timed b) (useNot.d.eval (Env.cons b Env.nil)) :=
  useNot.d_timedSim b

/-- A closure with a `let` at the function parameter. -/
noncomputable def useLet (b : Bool) : SPTree Bool := twice (fun x => let y := !x; y && x) b

derive_timed useLet

reflect_d useLet

/--
error: link_timed: the closure body
  (Tm.prim Prim.bnot (Tm.var Var.here)).letE (Tm.prim Prim.band ((Tm.var Var.here).pair (Tm.var Var.here.there)))
at a function parameter has a `let`: its β-step is not charged by the companion of `derive_timed`
link_timed: the route through the soundness theorem `Tm.dt_timedSim` does not apply either: the condition
  ((Tm.sample FTy.bool).rename (Ren.liftN [Ty.base FTy.bool, (Ty.base FTy.bool).arr (Ty.base FTy.bool)])).Pure
does not reduce to a true statement
-/
#guard_msgs in
link_timed useLet

end CatCrypt.Tactics.LinkTimedCertFnTest
