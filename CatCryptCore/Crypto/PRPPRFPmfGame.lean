/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PRPPRFSwitching
public import CatCryptCore.Crypto.NomPkgBridge

/-!
# Games given by a distribution on `Bool`

The game `PRPPRF.pmfGame p` returns a sample of `p` and leaves the heap unchanged.

## Main results

* `PRPPRF.pmfGame_isPure`, `PRPPRF.pmfGame_noFail` — it does not read or write the heap
  and never fails
* `PRPPRF.advantageA_pmfGame_le` — a distinguisher run on the output bit of two such
  games has advantage at most the advantage of the games
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PRPPRF

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto

/-- A game given by a distribution on `Bool` does not read or write the heap. -/
theorem pmfGame_isPure (p : PMF Bool) : SPComp.IsPure (pmfGame p) := by
  refine ⟨p.map some, fun h => ?_⟩
  simp only [pmfGame, SDistr.bind, PMF.bind_map, Function.comp_def, SDistr.pure]
  rw [PMF.map]; rfl

/-- A game given by a distribution on `Bool` never fails. -/
theorem pmfGame_noFail (p : PMF Bool) : SPComp.NoFail (pmfGame p) := fun _ => by
  simp [pmfGame, PMF.map_apply]

/-- A distinguisher run on the output bit of two games given by distributions on `Bool` has
advantage at most the advantage of the games. -/
theorem advantageA_pmfGame_le (p q : PMF Bool) (Z : Bool → SPComp Bool) :
    AdvantageA (pmfGame p) (pmfGame q) Z ≤ Advantage (pmfGame p) (pmfGame q) :=
  absDiff_bind_le_advantage (pmfGame_isPure p) (pmfGame_isPure q) (pmfGame_noFail p)
    (pmfGame_noFail q) Z Heap.empty

end CatCrypt.Crypto.PRPPRF
