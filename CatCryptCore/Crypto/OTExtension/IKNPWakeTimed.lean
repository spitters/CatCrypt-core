/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OTExtension.IKNPWake
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Tactics.DeriveReduction

/-!
# Costed form of the IKNP simulator over the scheduled base OTs

`derive_reduction` builds the costed form `simW.timed` of the multi-call simulator `simW` of
`IKNPWake.lean` over costed forms of the view completions `simS` and `simR`. The state of `simW`
and its port events hold functions, so the costed form runs on costed states and events (the
trees `simW.start.treeHat`, `simW.resume.treeHat`, `simW.finish.treeHat`), and its erasure
theorem `simW.erase_timed` states `MultiHybrid.Timed.ErasesHat`. No module imports this file.

## Main results

* `simW.timed`: the costed multi-call simulator.
* `simW.erase_timed`: its erasure through the erasure maps of the costed state and events.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.OT.IKNPWake.simW
