/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.SysRewrite
public import CatCryptCore.Tactics.AutoDispatchCore
public meta import CatCryptCore.Tactics.AutoDispatchCore

/-!
# `catcrypt_auto` shapes for trace equivalence and realizations at distance `0`

Registrations with the registry of `CatCryptCore.Tactics.AutoDispatchCore` for the goals that
need no state map: a trace equivalence closed by reflexivity or by a chain of known
equivalences, possibly under a common construction, and a realization at distance `0` that
reduces to one.

* `trace equivalence` (direct, priority 60), on `Sys.TraceEq _ _`: the arms
  `trace_eq_chain`, then `sys_congr` followed by `trace_eq_chain` or `assumption` on each
  component.
* `realization at distance zero` (direct, priority 55), on `Realizes _ _ _` and
  `RealizesSim _ _ _ _`: the same two arms behind `Sys.TraceEq.realizes`, resp.
  `Sys.TraceEq.realizesSim`.

An arm closes the goal or fails: a realization at a bound other than `fun _ _ => 0` does not
unify with the reduction to trace equivalence, so its arms fail and the normalised stage
runs. The registrations are active where this module is imported.

## Main results

* The shapes `trace equivalence` and `realization at distance zero` and their arms.
-/

public section

catcrypt_auto_shape "trace equivalence" direct priority 60 :=
  app CatCrypt.Crypto.UCTransparent.Sys.TraceEq

catcrypt_auto_shape "realization at distance zero" direct priority 55 :=
  any [app CatCrypt.Crypto.UCTransparent.Realizes, app CatCrypt.Crypto.UCTransparent.RealizesSim]

catcrypt_auto_arm "trace equivalence" order 10 := "trace_eq_chain"
catcrypt_auto_arm "trace equivalence" order 20 :=
  "(sys_congr; all_goals first | trace_eq_chain | assumption)"

catcrypt_auto_arm "realization at distance zero" order 10 := "trace_eq_chain"
catcrypt_auto_arm "realization at distance zero" order 20 :=
  "first
    | (refine CatCrypt.Crypto.UCTransparent.Sys.TraceEq.realizesSim ?_;
       sys_congr; all_goals first | trace_eq_chain | assumption)
    | (refine CatCrypt.Crypto.UCTransparent.Sys.TraceEq.realizes ?_;
       sys_congr; all_goals first | trace_eq_chain | assumption)"
