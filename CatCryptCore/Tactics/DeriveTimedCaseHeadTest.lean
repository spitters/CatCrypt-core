/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Core.SPTree

/-!
# Tests for a returned state holding functions under `derive_timed`

* `resumeT`: a tree returning the decision `resumeW`, whose body is an `if` on the state and a
  match on the answer, with leaves that return the state structure `Cf` (two function fields)
  unchanged or updated by `pendS`. The erasure theorem unfolds `resumeW` on the plain side.

## Main results

* `resumeT.erase_timed` — the erasure theorem of the costed tree, proved by the command
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedCaseHeadTest

open CatCrypt.Core

/-- A configuration with a data field and two function fields. -/
structure Cf where
  /-- The residual term. -/
  term : ℕ
  /-- The input queues. -/
  inq : ℕ → List ℕ
  /-- The adversarial queues. -/
  advq : Bool → List ℕ

/-- The configuration after a pending step. -/
def pendS (d : Cf) (p : Option Bool) (m : ℕ) : Cf :=
  match p with
  | none => d
  | some _ => { d with term := d.term + m }

/-- A resume decision: an `if` on the state, then a match on the answer. -/
def resumeW (s : Cf × Bool × Option Bool) (o : Option ℕ) :
    (Cf × Bool × Option Bool) × (Unit ⊕ Option ℕ) :=
  if s.2.1 then ((s.1, false, none), .inr none)
  else match o with
    | some m => ((pendS s.1 s.2.2 m, false, none), .inr (some m))
    | none => ((s.1, false, s.2.2), .inl ())

/-- The tree of the resume decision. -/
def resumeT (s : Cf × Bool × Option Bool) (o : Option ℕ) :
    SPTree ((Cf × Bool × Option Bool) × (Unit ⊕ Option ℕ)) :=
  SPTree.ret (resumeW s o)

derive_timed resumeT

end CatCrypt.Tactics.DeriveTimedCaseHeadTest
