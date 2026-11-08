/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.DeriveTimed.Basic
public import CatCryptCore.Tactics.StdCosts
import CatCryptCore.Core.SPTree

/-!
# Tests for function-valued case analyses and `let`s in `derive_timed`

Fresh reductions whose state is a function updated by `Function.update`:

* a queue per key updated behind a match on an event (`qStep`): the match is charged at the
  step, and the companion of the updated queues is one plus the old companion off the updated
  key;
* a `let` of an updated queue (`qLet`) and of the queues after an event (`qLetM`), read twice:
  the append is charged once, at the `let`;
* a table filled lazily behind a match on its entry (`tQuery`);
* a closure written in the source (`qClo`), whose companion keeps the append at each read.

Each erasure theorem and each derived cost is pinned by an `example`.
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedFnCaseTest

open CatCrypt.Core

/-- An event of a queue per key. -/
inductive QEv where
  | put (k v : ℕ)
  | tick

/-- The queues `q` after the event `e`. -/
def qEnq (q : ℕ → List ℕ) : QEv → ℕ → List ℕ
  | .put k v => Function.update q k (q k ++ [v])
  | .tick => q

/-- One step: the updated queues passed on. -/
noncomputable def qStep (q : ℕ → List ℕ) (e : QEv) (D : (ℕ → List ℕ) → SPTree Bool) :
    SPTree Bool :=
  (SPTree.ret (qEnq q e)).bind D

derive_timed qStep

example (q : ℕ → List ℕ) (qCost : ℕ → ℕ) (e : QEv) (D : (ℕ → List ℕ) → SPTree.Timed Bool)
    (DCost : (ℕ → List ℕ) → ℕ) :
    (qStep.timed q qCost e D DCost).2.erase = qStep q e (fun g => (D g).erase) :=
  qStep.erase_timed q qCost e D DCost

/-- The match on the event is charged at the step, the append once; the companion of the
updated queues is one plus the old companion off the updated key. -/
example (q : ℕ → List ℕ) (qCost : ℕ → ℕ) (k v : ℕ) (D : (ℕ → List ℕ) → SPTree.Timed Bool)
    (DCost : (ℕ → List ℕ) → ℕ) :
    qStep.timed q qCost (.put k v) D DCost =
      SPTree.Timed.delay (2 + (1 + (List.append.timedCost (q k) [v] + (1 + qCost k))))
        ((SPTree.Timed.ret (Function.update q k (q k ++ [v]),
            fun a => 2 + if a = k then 0 else 1 + qCost a)).bind
          fun a => (1 + DCost a.1, D a.1)) := rfl

/-- A `let` of an updated queue read twice. -/
noncomputable def qLet (q : ℕ → List ℕ) (k v a b : ℕ) (D : ℕ → SPTree Bool) : SPTree Bool :=
  let g := Function.update q k (q k ++ [v])
  D ((g a).length + (g b).length)

derive_timed qLet

example (q : ℕ → List ℕ) (qCost : ℕ → ℕ) (k v a b : ℕ) (D : ℕ → SPTree.Timed Bool)
    (DCost : ℕ → ℕ) :
    (qLet.timed q qCost k v a b D DCost).2.erase = qLet q k v a b (fun n => (D n).erase) :=
  qLet.erase_timed q qCost k v a b D DCost

/-- The append is charged once, at the `let`; each read costs one plus the companion. -/
example (q : ℕ → List ℕ) (qCost : ℕ → ℕ) (k v a b : ℕ) (D : ℕ → SPTree.Timed Bool)
    (DCost : ℕ → ℕ) :
    (qLet.timed q qCost k v a b D DCost).1 =
      1 + (List.append.timedCost (q k) [v] + (1 + qCost k)) +
        (1 + (DCost ((Function.update q k (q k ++ [v]) a).length +
            (Function.update q k (q k ++ [v]) b).length) +
          (1 + ((1 + (List.length.timedCost (Function.update q k (q k ++ [v]) a) +
              (1 + (2 + if a = k then 0 else 1 + qCost a)))) +
            (1 + (List.length.timedCost (Function.update q k (q k ++ [v]) b) +
              (1 + (2 + if b = k then 0 else 1 + qCost b)))))))) := rfl

/-- A `let` of the queues after an event, read twice. -/
noncomputable def qLetM (q : ℕ → List ℕ) (e : QEv) (a b : ℕ) (D : ℕ → SPTree Bool) :
    SPTree Bool :=
  let g := qEnq q e
  D ((g a).length + (g b).length)

derive_timed qLetM

example (q : ℕ → List ℕ) (qCost : ℕ → ℕ) (e : QEv) (a b : ℕ) (D : ℕ → SPTree.Timed Bool)
    (DCost : ℕ → ℕ) :
    (qLetM.timed q qCost e a b D DCost).2.erase = qLetM q e a b (fun n => (D n).erase) :=
  qLetM.erase_timed q qCost e a b D DCost

/-- The match and the append are charged once, at the `let`. -/
example (q : ℕ → List ℕ) (qCost : ℕ → ℕ) (k v a b : ℕ) (D : ℕ → SPTree.Timed Bool)
    (DCost : ℕ → ℕ) :
    (qLetM.timed q qCost (.put k v) a b D DCost).1 =
      2 + (1 + (List.append.timedCost (q k) [v] + (1 + qCost k))) +
        (1 + (DCost ((Function.update q k (q k ++ [v]) a).length +
            (Function.update q k (q k ++ [v]) b).length) +
          (1 + ((1 + (List.length.timedCost (Function.update q k (q k ++ [v]) a) +
              (1 + (2 + if a = k then 0 else 1 + qCost a)))) +
            (1 + (List.length.timedCost (Function.update q k (q k ++ [v]) b) +
              (1 + (2 + if b = k then 0 else 1 + qCost b)))))))) := rfl

/-- A table filled lazily: the entry at `x` set when absent. -/
def tFill (tab : ℕ → Option ℕ) (x y : ℕ) : ℕ → Option ℕ :=
  match tab x with
  | some _ => tab
  | none => Function.update tab x (some (y + y))

/-- One query of the table, the filled table passed on. -/
noncomputable def tQuery (tab : ℕ → Option ℕ) (x y : ℕ) (D : (ℕ → Option ℕ) → SPTree Bool) :
    SPTree Bool :=
  (SPTree.ret (tFill tab x y)).bind D

derive_timed tQuery

example (tab : ℕ → Option ℕ) (tabCost : ℕ → ℕ) (x y : ℕ)
    (D : (ℕ → Option ℕ) → SPTree.Timed Bool) (DCost : (ℕ → Option ℕ) → ℕ) :
    (tQuery.timed tab tabCost x y D DCost).2.erase = tQuery tab x y (fun g => (D g).erase) :=
  tQuery.erase_timed tab tabCost x y D DCost

/-- On a missing entry the sum is charged at the query, and the filled table has the
companion of an update. -/
example (tab : ℕ → Option ℕ) (tabCost : ℕ → ℕ) (x y : ℕ)
    (D : (ℕ → Option ℕ) → SPTree.Timed Bool) (DCost : (ℕ → Option ℕ) → ℕ)
    (h : tab x = none) :
    tQuery.timed tab tabCost x y D DCost =
      SPTree.Timed.delay (2 + (1 + tabCost x + 1))
        ((SPTree.Timed.ret (Function.update tab x (some (y + y)),
            fun a => 2 + if a = x then 0 else 1 + tabCost a)).bind
          fun a => (1 + DCost a.1, D a.1)) := by
  simp only [tQuery.timed, h]
  rfl

/-- A closure written in the source: each read evaluates the append. -/
noncomputable def qClo (q : ℕ → List ℕ) (k v : ℕ) (D : (ℕ → List ℕ) → SPTree Bool) :
    SPTree Bool :=
  (SPTree.ret (fun a => Function.update q k (q k ++ [v]) a)).bind D

derive_timed qClo

/-- The closure keeps the append in its companion: rule (a) does not hoist into closures
written in the source. -/
example (q : ℕ → List ℕ) (qCost : ℕ → ℕ) (k v : ℕ) (D : (ℕ → List ℕ) → SPTree.Timed Bool)
    (DCost : (ℕ → List ℕ) → ℕ) :
    qClo.timed q qCost k v D DCost =
      (SPTree.Timed.ret (fun a => Function.update q k (q k ++ [v]) a,
          fun a => 1 + (1 + (List.append.timedCost (q k) [v] + (1 + qCost k)) +
            (1 + if a = k then 0 else 1 + qCost a)))).bind
        fun a => (1 + DCost a.1, D a.1) := rfl

end CatCrypt.Tactics.DeriveTimedFnCaseTest

end
