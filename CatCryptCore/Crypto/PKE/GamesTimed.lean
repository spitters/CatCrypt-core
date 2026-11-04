/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PKE.Games
public import CatCryptCore.Tactics.DeriveTimedStructure

/-!
# The costed mirrors of the OW-PCA and labelled IND-CCA adversaries

`OWPCAAdversary.Timed` and `ROMOWPCAAdversary.Timed`, the costed mirrors by
`derive_timed_structure`: the computation field `run` becomes a costed tree with its cost
companion and the query-bound fields are dropped. They are the result types of the costed forms
of reductions that build an OW-PCA adversary (`FOTransform.uRedROM`, `FIPS203.redROM`,
`FIPS203.redFix`). `ROMLabelCCAAdversary.Timed` is the result type of the costed forms of
reductions that build a labelled IND-CCA adversary in the random-oracle model
(`Messaging.SealedSender.senderAnonROMReduction`).

## Main definitions

* `OWPCAAdversary.Timed`, `OWPCAAdversary.Timed.Erases`, `OWPCAAdversary.Timed.TimeBound`
* `ROMOWPCAAdversary.Timed`, `ROMOWPCAAdversary.Timed.Erases`,
  `ROMOWPCAAdversary.Timed.TimeBound`
* `ROMLabelCCAAdversary.Timed`, `ROMLabelCCAAdversary.Timed.Erases`,
  `ROMLabelCCAAdversary.Timed.TimeBound`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PKE.Games

derive_timed_structure OWPCAAdversary

derive_timed_structure ROMOWPCAAdversary

derive_timed_structure ROMLabelCCAAdversary

end CatCrypt.Crypto.PKE.Games
