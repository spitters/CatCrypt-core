/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNLogicForking
import all CatCryptCore.Unary.ExpectedCost

/-!
# Witness of the soundness of the rewinding extractor

`forkExtractor_sound` concludes the relation from a nonzero-probability output `some w` of the
rewinding extractor. The theorem here applies it to the Σ-protocol over `Unit` whose relation
holds everywhere and to the adversary that outputs its forgery without a query: the extractor
with one attempt at price `0` returns `some ()` at cost `0` and the empty heap with probability
`1`, so the hypothesis holds.

## Main results

* `unitSigma`, `unitAdversary` — the Σ-protocol over `Unit` and the query-free adversary
* `forkExtractor_unit_support` — the extractor returns `some ()` with nonzero probability
* `forkExtractor_sound_witness` — `forkExtractor_sound` at that support point
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Unary

/-- The Σ-protocol whose types are all `Unit`, whose relation holds everywhere and whose
verifier accepts every transcript. -/
noncomputable abbrev unitSigma : FiatShamirROM.Sigma where
  Stmt := Unit
  Wit := Unit
  Com := Unit
  Ch := Unit
  Resp := Unit
  Rand := Unit
  SimRand := Unit
  rel _ _ := True
  gen := PMF.pure ((), ())
  commit _ _ _ := ()
  respond _ _ _ _ := ()
  verify _ _ _ _ := true
  simulate _ _ _ := ((), ())
  extract _ _ _ _ _ _ := ()

/-- The EUF-CMA adversary against `unitSigma` on messages `Unit` that outputs the forgery
`((), ((), ()))` without a query. -/
noncomputable def unitAdversary : Adversary unitSigma Unit 0 0 where
  run _ := .ret ((), ((), ()))
  isQueryBound _ := trivial

/-- The rewinding extractor of `unitAdversary` with one attempt at price `0` returns `some ()`
at cost `0` and the empty heap with nonzero probability. -/
theorem forkExtractor_unit_support :
    (forkExtractor unitAdversary 0 () 1 Heap.empty) (some ((some (), 0), Heap.empty)) ≠ 0 := by
  have hc : checkW (P := unitSigma) () = Function.const _ (some (() : unitSigma.Wit)) := by
    funext w
    simp only [checkW, unitSigma]
    rfl
  simp only [forkExtractor, forkAttempt, retryN, hc, PMF.map_const]
  simp [CostComp.lift, CostComp.bind, CostComp.pure, liftPMF, SPComp.bind, SPComp.pure,
    SDistr.bind, SDistr.pure]

/-- `forkExtractor_sound` at `unitAdversary`, the price `0`, one attempt and the support point
`some ()` of `forkExtractor_unit_support`: the hypothesis holds and the relation follows. -/
theorem forkExtractor_sound_witness :
    (forkExtractor unitAdversary 0 () 1 Heap.empty) (some ((some (), 0), Heap.empty)) ≠ 0 ∧
      unitSigma.rel () () :=
  ⟨forkExtractor_unit_support,
    forkExtractor_sound unitAdversary 0 () 1 Heap.empty () 0 Heap.empty
      forkExtractor_unit_support⟩

end CatCrypt.Crypto.FiatShamirROM
