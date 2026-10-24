/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Crypto.UCConcrete
import CatCryptCore.Core.SPTree

/-!
# Tests for a state with function fields read from an environment's input

A reduction in the shape of `branchReduction` applied to an environment
`Z : Env (Unit × EnvState) β` whose input carries a state structure with function fields: the
prefix applies a function field of `Z.input.2` to an argument, binds handler calls and returns
the updated state, the post step returns a pair holding the state, and the distinguisher runs
on it. The input `Z.input` is a data path: its costed value is read from the binder
`inputHat` of the costed form.

## Main results

* `envRed.timeBound` — the time of the costed form of `envRed`
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedEnvStateTest

open CatCrypt.Core CatCrypt.Crypto.UCConcrete

/-- A state with function fields. -/
structure EnvState where
  /-- The password of each user. -/
  pwdFile : ℕ → Option ℕ
  /-- The status of each session. -/
  status : ℕ → Bool

/-- The state with the status of `sid` set. -/
def EnvState.setStatus (s : EnvState) (sid : ℕ) : EnvState where
  pwdFile := s.pwdFile
  status := Function.update s.status sid true

/-- The environment's state read from its input, a function field applied, two handler calls
whose tree returns the updated state, and the distinguisher on the pair of the key and the
state unless the key is the adversary's (the shape of `branchReduction` applied to the gated
prefix and post step). -/
noncomputable def envRed (handler : ℕ → SPTree ℕ) (sid uid : ℕ)
    (Z : Env (Unit × EnvState) ((Unit ⊕ ℕ) × EnvState))
    (dist : (Unit ⊕ ℕ) × EnvState → SPTree Bool) (o : ℕ) : SPTree Bool :=
  .load Z.heap <|
    let s := Z.input.2
    ((handler ((s.pwdFile uid).getD 0)).bind fun g =>
      (handler (g + sid)).bind fun k => .ret (s.setStatus sid, k)).bind fun r =>
    if r.2 = o then .ret false else dist (Sum.inr r.2, r.1)

derive_timed envRed

/-- The costed form of `envRed` takes the costed value `inputHat` of the data path `Z.input`
after the binders of `envRed`. -/
example (handler : ℕ → SPTree.Timed ℕ) (handlerCost : ℕ → ℕ) (sid uid : ℕ)
    (Z : Env (Unit × EnvState) ((Unit ⊕ ℕ) × EnvState))
    (dist : (Unit ⊕ ℕ) × EnvState → SPTree.Timed Bool)
    (distCost : (Unit ⊕ ℕ) × EnvState → ℕ) (o : ℕ)
    (inputHat : Unit × ((ℕ → Option ℕ) × (ℕ → ℕ)) × (ℕ → Bool) × (ℕ → ℕ)) :
    (envRed.timed handler handlerCost sid uid Z dist distCost o inputHat).2.erase =
      envRed (fun x => (handler x).erase) sid uid Z (fun y => (dist y).erase) o :=
  envRed.erase_timed handler handlerCost sid uid Z dist distCost o inputHat

/-- The time of the costed form of `envRed`: the heap reset, two handler calls, the
distinguisher, the companion of `pwdFile` read from `inputHat`, and twenty steps. -/
theorem envRed.timeBound (handler : ℕ → SPTree.Timed ℕ) (handlerCost : ℕ → ℕ) (sid uid : ℕ)
    (Z : Env (Unit × EnvState) ((Unit ⊕ ℕ) × EnvState))
    (dist : (Unit ⊕ ℕ) × EnvState → SPTree.Timed Bool)
    (distCost : (Unit ⊕ ℕ) × EnvState → ℕ) (o : ℕ)
    (inputHat : Unit × ((ℕ → Option ℕ) × (ℕ → ℕ)) × (ℕ → Bool) × (ℕ → ℕ))
    {t c T a p : ℕ} (hH : ∀ x, (handler x).time ≤ t) (hh : ∀ x, handlerCost x ≤ c)
    (hD : ∀ y, (dist y).time ≤ T) (hd : ∀ y, distCost y ≤ a)
    (hp : ∀ x, inputHat.2.1.2 x ≤ p) :
    SPTree.Timed.stepTime (envRed.timed handler handlerCost sid uid Z dist distCost o inputHat) ≤
      Z.heap.data.keys.card + 2 * t + 2 * c + T + a + p + 20 := by
  have key : ∀ {β : Type} (X : ℕ) (P : ℕ × SPTree.Timed β)
      (f : β → ℕ × SPTree.Timed Bool),
      X ≤ c + p + 4 → SPTree.Timed.stepTime P ≤ 2 * t + c + 4 →
      (∀ x, SPTree.Timed.stepTime (f x) ≤ T + a + 3) →
      0 + (1 + Z.heap.data.keys.card + (X + P.1 + (P.2.bind f).1 + (P.2.bind f).2.time)) ≤
        Z.heap.data.keys.card + 2 * t + 2 * c + T + a + p + 20 := by
    intro β X P f hX hP hf
    have hq := SPTree.Timed.stepTime_bind_le P.2 f _ hf
    simp only [SPTree.Timed.stepTime] at hq hP
    omega
  simp only [envRed.timed, SPTree.Timed.stepTime, SPTree.Timed.time_load]
  refine key _ _ _ ?_ ?_ (fun x => ?_)
  · have := hh ((Z.input.2.pwdFile uid).getD 0)
    have := hp uid
    omega
  · time_bound
  · time_bound

/-- The same state read from the input with its field applied, and the state passed to the
distinguisher as an argument only: no costed value of `Z.input` is demanded, and the applied
field keeps the convention of field paths (`pwdFileCost`). -/
noncomputable def envRedApp (handler : ℕ → SPTree ℕ) (sid uid : ℕ)
    (Z : Env (Unit × EnvState) ((Unit ⊕ ℕ) × EnvState))
    (dist : (Unit ⊕ ℕ) × EnvState → SPTree Bool) (o : ℕ) : SPTree Bool :=
  .load Z.heap <|
    let s := Z.input.2
    (handler ((s.pwdFile uid).getD 0)).bind fun g =>
    (handler (g + sid)).bind fun k =>
    if k = o then .ret false else dist (Sum.inr k, s.setStatus sid)

derive_timed envRedApp

example (handler : ℕ → SPTree.Timed ℕ) (handlerCost : ℕ → ℕ) (sid uid : ℕ)
    (Z : Env (Unit × EnvState) ((Unit ⊕ ℕ) × EnvState))
    (dist : (Unit ⊕ ℕ) × EnvState → SPTree.Timed Bool)
    (distCost : (Unit ⊕ ℕ) × EnvState → ℕ) (o : ℕ) (pwdFileCost : ℕ → ℕ) :
    (envRedApp.timed handler handlerCost sid uid Z dist distCost o pwdFileCost).2.erase =
      envRedApp (fun x => (handler x).erase) sid uid Z (fun y => (dist y).erase) o :=
  envRedApp.erase_timed handler handlerCost sid uid Z dist distCost o pwdFileCost

/-- The environment with the state component of its input and output dropped. -/
noncomputable def dropSt {α β S : Type} (Z : Env (α × S) (β × S)) : Env α β :=
  ⟨Z.input.1, Z.heap, fun y => Z.dist (y, Z.input.2)⟩

/-- A `let` of an environment whose input is a function into `SPComp`, which has no costed
form; the body reads only the heap of the environment. -/
noncomputable def envRedFn (Z : Env ((ℕ → ℕ → ℕ → SPComp Bool) × Unit) (Bool × Unit))
    (t : ℕ → ℕ → ℕ → SPTree Bool) (x y z : ℕ) : SPTree Bool :=
  let Z' := Env.postcomp (fun b => SPComp.pure b) (dropSt Z)
  .load Z'.heap (t x y z)

derive_timed envRedFn

example (Z : Env ((ℕ → ℕ → ℕ → SPComp Bool) × Unit) (Bool × Unit))
    (t : ℕ → ℕ → ℕ → SPTree.Timed Bool) (tCost : ℕ → ℕ → ℕ → ℕ) (x y z : ℕ) :
    (envRedFn.timed Z t tCost x y z).2.erase = envRedFn Z (fun a b c => (t a b c).erase) x y z :=
  envRedFn.erase_timed Z t tCost x y z

end CatCrypt.Tactics.DeriveTimedEnvStateTest
