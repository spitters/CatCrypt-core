/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DerivePMF

/-!
# Tests for the eliminator rules of `derive_timed` on distributions

* `answerAll A`: the output distribution of the adversary `A` whose queries are answered by
  uniform bits, by structural recursion over `A`. The reflection defines the tree
  `answerAll.pmfTree` by the same recursion (a `rand` node at each sample of `A`, a `rand` node
  at each uniform answer) and `answerAll.dist_pmfTree` by the recursion of its proof; the costed
  form is derived by the rules of `derive_timed` (`answerAll.erase_timed`).
* `elimDist o`: a distribution written with the case analysis `Sum.rec` of a sum: the same case
  analysis over the trees of its alternatives (`elimDist.dist_pmfTree`, `elimDist.erase_timed`).
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DerivePMFRecTest

open CatCrypt.Crypto

/-- The output of the adversary `A` with its queries answered by uniform bits. -/
noncomputable def answerAll : OracleAdv ℕ Bool Bool → PMF Bool
  | .ret b => PMF.pure b
  | .rand p k => p.bind fun x => answerAll (k x)
  | .query _ k => (PMF.uniformFintype Bool).bind fun r => answerAll (k r)

derive_timed answerAll

/-- At a query of `A`: the unit of the case analysis, a uniform answer at one `rand` node, and
the costed recursive call at the answer behind the step cost of the source node. -/
theorem answerAll_timed_query (d : ℕ) (c : Bool → ℕ) (k : Bool → OracleAdv.Timed ℕ Bool Bool) :
    answerAll.timed (.query d c k) = OracleAdv.Timed.delay 1
      ((OracleAdv.Timed.rand (PMF.uniformFintype Bool) (fun _ => 0) fun x => .ret x).bind
        fun x => OracleAdv.Timed.delay (2 + c x) (answerAll.pmfTree.timed (k x))) := by
  rw [answerAll.timed, answerAll.pmfTree.timed]

/-- At a sample of `A`: the sample is a `rand` node of the costed tree, at its unit. -/
theorem answerAll_timed_rand {β : Type} (p : PMF β) (c : β → ℕ)
    (k : β → OracleAdv.Timed ℕ Bool Bool) :
    answerAll.timed (.rand p c k) = (1, .rand p (fun x => 2 + c x + (answerAll.pmfTree.timed (k x)).1)
      fun x => (answerAll.pmfTree.timed (k x)).2) := by
  rw [answerAll.timed, answerAll.pmfTree.timed]

/-- The tree has the distribution of `answerAll`, for every adversary. -/
example (A : OracleAdv ℕ Bool Bool) : (answerAll.pmfTree A).dist = answerAll A :=
  answerAll.dist_pmfTree A

/-- A distribution by the case analysis of a sum. -/
noncomputable def elimDist (o : ℕ ⊕ Bool) : PMF ℕ :=
  Sum.rec (motive := fun _ => PMF ℕ) (fun n => PMF.pure (n + 1))
    (fun b => (PMF.uniformFintype Bool).map fun x => if x = b then 0 else 1) o

derive_timed elimDist

/-- The erasure theorem of the case analysis. -/
example (o : ℕ ⊕ Bool) : (elimDist.timed o).2.erase.dist = elimDist o := elimDist.erase_timed o

end CatCrypt.Tactics.DerivePMFRecTest
