/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Crypto.UCConcrete
public import CatCryptCore.Tactics.DeriveReduction
import CatCryptCore.Core.SPTree

/-!
# Tests of `time_bound` on continuations bounded under a leaf invariant

A prefix `pfx` returns a state whose function field `pwdFile` is updated under an `if` on a
corruption bit, from a state passed in with the cost companion `inputHat` of the update; the
reduction `red` resets the heap, calls `pfx` on the state of an environment's input and runs a
post step that applies the returned field, so that its cost reads the companion of the
returned state. The continuation is bounded only at the values `pfx` can return: `time_bound`
infers the leaf invariant `∀ u, r.1.1.2 u ≤ p + 3` from the hypothesis `∀ x, inputHat x ≤ p`
and proves it by traversing the leaves of `pfx`.

## Main results

* `pfx_bind_time`, `pfx_prefix_bind_time` — a bind after `pfx` whose continuation reads the
  companion of the returned state, without and with the step cost of `pfx` on the path
* `red.timeBound` — the time of the costed form of `red`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.AutoTimeAllRetTest

open CatCrypt.Core CatCrypt.Crypto.UCConcrete

/-- A state with function fields. -/
structure St where
  /-- The password of each user. -/
  pwdFile : ℕ → Option ℕ
  /-- The status of each session. -/
  status : ℕ → Bool

/-- The state with the password of `u` removed. -/
def St.corrupt (s : St) (u : ℕ) : St where
  pwdFile := Function.update s.pwdFile u none
  status := s.status

/-- The state with the status of `sid` set. -/
def St.setStatus (s : St) (sid : ℕ) : St where
  pwdFile := s.pwdFile
  status := Function.update s.status sid true

/-- A corruption query and a handler call, returning the state corrupted at `uid` when the
query answers `true`. -/
noncomputable def pfx (handler : ℕ → SPTree ℕ) (corr : ℕ → SPTree Bool) (sid uid : ℕ)
    (s : St) : SPTree (St × ℕ) :=
  (corr uid).bind fun b =>
    (handler sid).bind fun k => .ret (if b then s.corrupt uid else s, k)

derive_timed pfx

/-- The heap reset, `pfx` on the state of the environment's input, and the distinguisher on
the password field of the returned state applied to `uid`. -/
noncomputable def red (handler : ℕ → SPTree ℕ) (corr : ℕ → SPTree Bool) (sid uid : ℕ)
    (Z : Env (Unit × St) ((Unit ⊕ ℕ) × St))
    (dist : (Unit ⊕ ℕ) × St → SPTree Bool) : SPTree Bool :=
  .load Z.heap <|
    (pfx handler corr sid uid Z.input.2).bind fun r =>
    dist (Sum.inr ((r.1.pwdFile uid).getD r.2), r.1.setStatus sid)

derive_timed red

/-- A bind after `pfx` whose continuation costs the companion of the returned password field
at `uid`. -/
theorem pfx_bind_time (handler : ℕ → SPTree.Timed ℕ) (handlerCost : ℕ → ℕ)
    (corr : ℕ → SPTree.Timed Bool) (corrCost : ℕ → ℕ) (sid uid : ℕ) (s : St)
    (inputHat : ℕ → ℕ)
    {t c q e p : ℕ} (hH : ∀ x, (handler x).time ≤ t) (hh : ∀ x, handlerCost x ≤ c)
    (hC : ∀ x, (corr x).time ≤ q) (hc : ∀ x, corrCost x ≤ e)
    (hp : ∀ x, inputHat x ≤ p) :
    SPTree.Timed.stepTime ((pfx.timed handler handlerCost corr corrCost sid uid s
      inputHat).2.bind fun r => (r.1.1.2 uid, .ret ())) ≤ t + c + q + e + p + 30 := by
  time_bound

/-- The same bind with the step cost of `pfx` on the path. -/
theorem pfx_prefix_bind_time (handler : ℕ → SPTree.Timed ℕ) (handlerCost : ℕ → ℕ)
    (corr : ℕ → SPTree.Timed Bool) (corrCost : ℕ → ℕ) (sid uid : ℕ) (s : St)
    (inputHat : ℕ → ℕ)
    {t c q e p : ℕ} (hH : ∀ x, (handler x).time ≤ t) (hh : ∀ x, handlerCost x ≤ c)
    (hC : ∀ x, (corr x).time ≤ q) (hc : ∀ x, corrCost x ≤ e)
    (hp : ∀ x, inputHat x ≤ p) :
    (pfx.timed handler handlerCost corr corrCost sid uid s inputHat).1 +
    SPTree.Timed.stepTime ((pfx.timed handler handlerCost corr corrCost sid uid s
      inputHat).2.bind fun r => (r.1.1.2 uid, .ret ())) ≤ t + c + q + e + p + 30 := by
  time_bound

/-- The time of the costed form of `red`: the heap reset, the corruption query, the handler
call, the companion of the returned password field and the distinguisher. -/
theorem red.timeBound (handler : ℕ → SPTree.Timed ℕ) (handlerCost : ℕ → ℕ)
    (corr : ℕ → SPTree.Timed Bool) (corrCost : ℕ → ℕ) (sid uid : ℕ)
    (Z : Env (Unit × St) ((Unit ⊕ ℕ) × St))
    (dist : (Unit ⊕ ℕ) × St → SPTree.Timed Bool)
    (distCost : (Unit ⊕ ℕ) × St → ℕ) (inputHat : ℕ → ℕ)
    {t c q e T a p : ℕ} (hH : ∀ x, (handler x).time ≤ t) (hh : ∀ x, handlerCost x ≤ c)
    (hC : ∀ x, (corr x).time ≤ q) (hc : ∀ x, corrCost x ≤ e)
    (hD : ∀ y, (dist y).time ≤ T) (hd : ∀ y, distCost y ≤ a)
    (hp : ∀ x, inputHat x ≤ p) :
    SPTree.Timed.stepTime (red.timed handler handlerCost corr corrCost sid uid Z dist distCost
      inputHat) ≤ Z.heap.data.keys.card + t + c + q + e + T + a + p + 30 := by
  time_bound

end CatCrypt.Tactics.AutoTimeAllRetTest

end
