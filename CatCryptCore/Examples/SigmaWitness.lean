/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.Sigma

/-!
# Witness of completeness of the example Σ-protocol

`simpleSigma_completeness` quantifies over the pairs in the relation of `simpleSigma`. The theorem
here applies it at the statement, witness and challenge `true`, `true`, `false`, whose membership
in the relation holds by definition.

## Main results

* `simpleSigma_completeness_witness` — the honest transcript at these values is accepted
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.Sigma

open CatCrypt.Core

/-- The honest transcript of `simpleSigma` at the statement `true`, the witness `true` and the
challenge `false` is accepted. -/
theorem simpleSigma_completeness_witness :
    CatCrypt.Unary.pHoare (fun _ => True) (realTranscriptGiven simpleSigma true true false)
      (fun t _ => simpleSigma.verify true t.message false t.response = true) :=
  simpleSigma_completeness true true false rfl

end CatCrypt.Examples.Sigma
