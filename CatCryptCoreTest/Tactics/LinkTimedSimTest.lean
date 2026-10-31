/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.LinkTimed
public import CatCryptCore.Crypto.UCGlobalPipeTimed
public import CatCryptCore.Crypto.GeneralForkingLemmaTimed

/-!
# Tests of `link_timed` on simulator steps with proof binders and on table samples

* The steps `start` and `resume` of the post-processing simulator `MultiHybrid.postSim` of
  `CatCryptCore.Crypto.UCGlobalPipe` take the post-processing `f` and its no-fail proof
  `hf : ∀ o, NoFail (f o)`. Both are binders of the theorems of `reflect_d` only: `hf` is a
  proof and `f` is mentioned by the step trees only through the type of `hf`; `link_timed`
  keeps `f` with its companion `fCost`. `start` is linked at allowance `0`.
* The coin stage of `GeneralForkingLemma.guessReduction` samples a table `Fin q → R`, the
  finite ground type `FTy.tab q RF` of D, in one sample node; its costed form ends with the
  projection of the costed table onto the plain one (`TSim.bindRet`). Allowance `2`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.MultiHybrid

reflect_d postSim.start.tree

link_timed postSim.start

example := @postSim.start.tree.d_timedSim

reflect_d postSim.resume.tree

link_timed postSim.resume

example := @postSim.resume.tree.d_cost_le

end CatCrypt.Crypto.UCTransparent.MultiHybrid

namespace CatCrypt.Crypto.GeneralForkingLemma

reflect_d guessReduction.coins.tree

link_timed guessReduction.coins

example := @guessReduction.coins.tree.d_cost_le

end CatCrypt.Crypto.GeneralForkingLemma
