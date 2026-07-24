/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.Commitments.CommitmentScheme

/-!
# Abstract Polynomial Commitment Schemes

This file extends the abstract commitment scheme with evaluation opening:
the prover can demonstrate that a committed polynomial evaluates to a claimed
value at a given point, without revealing the polynomial.

## Main definitions

* `PolyCommitScheme` — Extends `CommitmentScheme` with evaluation witness creation and verification
* `EvalCorrect_Game` — Evaluation correctness game
* `EvalBinding_Game` — Evaluation binding game
* `PolyBinding_Game` — Polynomial binding game

## References

* [SSProve/Commitments — PolyCom.v](https://github.com/SSProve/Commitments)
* [Kate, Zaverucha, Goldberg, 2010 — §3.2]
-/

namespace CatCrypt.Examples.Commitments

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## Polynomial Commitment Scheme Structure -/

/-- An abstract polynomial commitment scheme.

Extends `CommitmentScheme` with:
- An evaluation point type
- An evaluation value type
- A witness type for evaluation proofs
- `create_witness`: creates a proof that `φ(z) = y`
- `verify_eval`: checks the evaluation proof -/
structure PolyCommitScheme extends CommitmentScheme where
  /-- Evaluation point type -/
  Point : Type
  /-- Evaluation value type -/
  Value : Type
  /-- Evaluation witness type -/
  Witness : Type
  [instFintypePoint : Fintype Point]
  [instNonemptyPoint : Nonempty Point]
  [instDecEqPoint : DecidableEq Point]
  [instFintypeValue : Fintype Value]
  [instNonemptyValue : Nonempty Value]
  [instDecEqValue : DecidableEq Value]
  [instFintypeWitness : Fintype Witness]
  [instNonemptyWitness : Nonempty Witness]
  [instDecEqWitness : DecidableEq Witness]
  /-- Create evaluation witness: given key, polynomial, and point, produce witness and value -/
  create_witness : Key → Message → Point → SPComp (Witness × Value)
  /-- Verify evaluation proof -/
  verify_eval : Key → Commitment → Point → Value → Witness → Bool

attribute [instance] PolyCommitScheme.instFintypePoint PolyCommitScheme.instNonemptyPoint
  PolyCommitScheme.instDecEqPoint PolyCommitScheme.instFintypeValue
  PolyCommitScheme.instNonemptyValue PolyCommitScheme.instDecEqValue
  PolyCommitScheme.instFintypeWitness PolyCommitScheme.instNonemptyWitness
  PolyCommitScheme.instDecEqWitness

variable (PS : PolyCommitScheme)

/-! ## Evaluation Correctness -/

/-- Evaluation correctness game: setup, commit, create witness, verify eval.
    Returns `true` if verify_eval accepts the honest evaluation proof. -/
noncomputable def EvalCorrect_Game (m : PS.Message) (z : PS.Point) : SPComp Bool := do
  let k ← PS.setup
  let (c, _o) ← PS.commit k m
  let (w, y) ← PS.create_witness k m z
  SPComp.pure (PS.verify_eval k c z y w)

/-! ## Polynomial Binding -/

/-- Polynomial binding adversary: given key, output two different polynomials
    that have the same commitment -/
abbrev PolyBindingAdversary :=
  PS.Key → SPComp (PS.Message × PS.Opening × PS.Message × PS.Opening × PS.Commitment)

/-- Polynomial binding game: adversary finds two polynomials with the same commitment.
    Same as `Binding_Game` for the underlying commitment scheme. -/
noncomputable def PolyBinding_Game (A : PolyBindingAdversary PS) : SPComp Bool :=
  Binding_Game PS.toCommitmentScheme A

/-! ## Evaluation Binding -/

/-- Evaluation binding adversary: given key, output a commitment and two valid
    evaluation openings at the same point with different values -/
abbrev EvalBindingAdversary :=
  PS.Key → SPComp (PS.Commitment × PS.Point × PS.Value × PS.Witness × PS.Value × PS.Witness)

/-- Evaluation binding game: adversary finds two valid evaluation openings
    at the same point with different values for the same commitment -/
noncomputable def EvalBinding_Game (A : EvalBindingAdversary PS) : SPComp Bool := do
  let k ← PS.setup
  let (c, z, y₁, w₁, y₂, w₂) ← A k
  SPComp.pure (decide (y₁ ≠ y₂ ∧ PS.verify_eval k c z y₁ w₁ ∧ PS.verify_eval k c z y₂ w₂))

/-- Evaluation binding advantage -/
noncomputable def EvalBinding_Advantage (A : EvalBindingAdversary PS) : ℝ≥0∞ :=
  prTrue (EvalBinding_Game PS A) Heap.empty

/-! ## Knowledge Soundness -/

/-- Knowledge soundness adversary: given key, output commitment C and evaluation proof (z, y, w).
    Extractor must recover the committed polynomial. -/
structure KnowledgeSoundnessAdversary where
  /-- Adversary produces commitment and evaluation opening -/
  run : PS.Key → SPComp (PS.Commitment × PS.Point × PS.Value × PS.Witness)

-- Knowledge soundness: for every adversary, there exists an extractor that
-- recovers the committed polynomial (defined later with AGM).

end CatCrypt.Examples.Commitments
