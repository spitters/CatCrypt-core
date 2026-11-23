/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.Sigma

/-!
# Witnesses of zero knowledge and soundness of the example Σ-protocol

`simpleSigma_shvzk` and `simpleSigma_shvzk_given` quantify over the pairs in the relation of
`simpleSigma`; the theorems here apply them at the statement and witness `true`, `true` (and the
challenge `false`), whose membership in the relation holds by definition.
`simpleSigma_special_sound` and `simpleSigma_binding` take two accepting openings of one
commitment under different challenges; `simpleSigmaDoubleOpening` is such a pair for the
statement `true`, and the theorems here extract a witness from it.

## Main definitions

* `simpleSigmaDoubleOpening` — the commitment `false` opened with responses `true` and `false`
  under the challenges `false` and `true`

## Main results

* `simpleSigma_shvzk_witness`, `simpleSigma_shvzk_given_witness` — real and simulated
  transcripts are equal in distribution at these values
* `simpleSigma_special_sound_witness`, `simpleSigma_binding_witness` — the statement `true` has
  a witness, extracted from `simpleSigmaDoubleOpening`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.Sigma

open CatCrypt.Core CatCrypt.Relational

/-- `simpleSigma_shvzk` at the statement `true` and the witness `true`. -/
theorem simpleSigma_shvzk_witness :
    rHoare (fun _ _ => True) (realTranscript simpleSigma true true)
      (simulatedTranscript simpleSigma true) (fun t₁ _ t₂ _ => t₁ = t₂) :=
  simpleSigma_shvzk true true rfl

/-- `simpleSigma_shvzk_given` at the statement `true`, the witness `true` and the challenge
`false`. -/
theorem simpleSigma_shvzk_given_witness :
    rHoare (fun _ _ => True) (realTranscriptGiven simpleSigma true true false)
      (simulatedTranscriptGiven simpleSigma true false) (fun t₁ _ t₂ _ => t₁ = t₂) :=
  simpleSigma_shvzk_given true true false rfl

/-- Two accepting openings of the commitment `false` for the statement `true` of `simpleSigma`:
the challenge `false` with the response `true`, and the challenge `true` with the response
`false`. -/
def simpleSigmaDoubleOpening : DoubleOpening simpleSigma true where
  commitment := false
  challenge₁ := false
  response₁ := true
  challenge₂ := true
  response₂ := false
  diff := by grind
  verify₁ := by decide
  verify₂ := by decide

/-- `simpleSigma_special_sound` at the two transcripts of `simpleSigmaDoubleOpening`: the
extractor returns a witness of the statement `true`. -/
theorem simpleSigma_special_sound_witness : ∃ w, simpleSigma.relation true w := by
  obtain ⟨ext, hext⟩ := simpleSigma_special_sound
  exact ⟨ext true simpleSigmaDoubleOpening.toTwoTranscripts,
    hext true simpleSigmaDoubleOpening.toTwoTranscripts⟩

/-- `simpleSigma_binding` at `simpleSigmaDoubleOpening`. -/
theorem simpleSigma_binding_witness : ∃ w, simpleSigma.relation true w :=
  simpleSigma_binding true simpleSigmaDoubleOpening

end CatCrypt.Examples.Sigma
