/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCInterleave
public import CatCryptCore.Crypto.UCFeedback
public import CatCryptCore.Crypto.UCGlobalSquare
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StdCosts

/-!
# Tests of dispatches on sums and match-dispatched steps

`derive_reduction` and `derive_time_bound` on reductions whose steps dispatch on their input:

* `elimRed`, `casesRed`, `recRed`: a computation `Sum.elim A B x`, `Sum.casesOn x A B` and
  `Sum.rec A B x` on a sum binder `x`;
* `sumStep`: a structure-valued reduction with a field `Sum.elim p.step q.step`;
* `MultiHybrid.tensor`: the tensor of two multi-call hybrids, whose three steps are
  `Sum.elim` dispatches on the port;
* `MultiHybrid.fbHybrid` and `gRouter`: multi-call hybrids whose steps are matches on one
  discriminant, on nested patterns and on two discriminants.

## Main results

* the costed forms, erasure theorems and time theorems emitted by the commands
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveSumMatchTest

open CatCrypt.Core

/-- The adversary `A` on a left input and `B` on a right input, by `Sum.elim`. -/
noncomputable def elimRed (x : ℕ ⊕ Bool) (A : ℕ → SPComp Bool) (B : Bool → SPComp Bool) :
    SPComp Bool :=
  Sum.elim A B x

derive_reduction elimRed
derive_time_bound elimRed.tree

/-- The adversary `A` on a left input and `B` on a right input, by `Sum.casesOn`. -/
noncomputable def casesRed (x : ℕ ⊕ Bool) (A : ℕ → SPComp Bool) (B : Bool → SPComp Bool) :
    SPComp Bool :=
  Sum.casesOn (motive := fun _ => SPComp Bool) x A B

derive_reduction casesRed
derive_time_bound casesRed.tree

/-- The adversary `A` on a left input and `B` on a right input, by `Sum.rec`. -/
noncomputable def recRed (x : ℕ ⊕ Bool) (A : ℕ → SPComp Bool) (B : Bool → SPComp Bool) :
    SPComp Bool :=
  Sum.rec (motive := fun _ => SPComp Bool) A B x

derive_reduction recRed
derive_time_bound recRed.tree

/-- A two-stage step: a step on an input and a decision on its output. -/
structure SumStep (E O : Type) where
  /-- The step on an input. -/
  step : E → SPComp O
  /-- The decision on an output. -/
  done : O → SPComp Bool

derive_timed_structure SumStep

/-- The step of `p` on a left input and the step of `q` on a right input, with the decision
of `p`. -/
noncomputable def sumStep {E E' O : Type} (p : SumStep E O) (q : SumStep E' O) :
    SumStep (E ⊕ E') O where
  step := Sum.elim p.step q.step
  done := p.done

derive_reduction sumStep
derive_time_bound sumStep.step.tree

end CatCrypt.Tactics.DeriveSumMatchTest

derive_reduction CatCrypt.Crypto.UCTransparent.MultiHybrid.tensor
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.tensor.start.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.tensor.resume.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.tensor.finish.tree

derive_reduction CatCrypt.Crypto.UCTransparent.MultiHybrid.fbHybrid
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.fbHybrid.start.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.fbHybrid.resume.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.fbHybrid.finish.tree

derive_reduction CatCrypt.Crypto.UCTransparent.gRouter
derive_time_bound CatCrypt.Crypto.UCTransparent.gRouter.start.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.gRouter.resume.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.gRouter.finish.tree

namespace CatCrypt.Tactics.DeriveSumMatchTest

open CatCrypt.Core

/-- The step of `sumStep` costs the larger of the bounds of the two dispatched steps plus the
dispatch. -/
example {E E' O : Type} (p : SumStep E O) (q : SumStep E' O) (step : E → SPTree.Timed O)
    (stepCost : E → ℕ) (step_2 : E' → SPTree.Timed O) (step_2Cost : E' → ℕ)
    (done : O → SPTree.Timed Bool) (doneCost : O → ℕ) (a : E ⊕ E') {T t T' t' Td td : ℕ}
    (h1 : ∀ a, (step a).time ≤ T) (h2 : ∀ a, stepCost a ≤ t)
    (h3 : ∀ a, (step_2 a).time ≤ T') (h4 : ∀ a, step_2Cost a ≤ t')
    (h5 : ∀ a, (done a).time ≤ Td) (h6 : ∀ a, doneCost a ≤ td) :
    SPTree.Timed.stepTime
        (sumStep.step.tree.timed p q step stepCost step_2 step_2Cost done doneCost a) ≤
      max (t + T + 1) (t' + T' + 1) + 2 :=
  sumStep.step.tree.timeBound_timed p q step stepCost step_2 step_2Cost done doneCost a
    h1 h2 h3 h4 h5 h6

/-- The `resume` step of the router, a match on two discriminants with nested patterns, costs
at most the larger bound of its alternatives plus the dispatch. -/
example (EH OH EA' OA' EG OG : Type) (s : Bool) (o : (OH ⊕ OA') ⊕ OG) :
    SPTree.Timed.stepTime
        (CatCrypt.Crypto.UCTransparent.gRouter.resume.tree.timed EH OH EA' OA' EG OG s o) ≤
      max 0 2 + 2 :=
  CatCrypt.Crypto.UCTransparent.gRouter.resume.tree.timeBound_timed EH OH EA' OA' EG OG s o

end CatCrypt.Tactics.DeriveSumMatchTest
