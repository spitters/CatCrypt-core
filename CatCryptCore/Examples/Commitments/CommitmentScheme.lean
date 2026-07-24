/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Code
import CatCryptCore.Crypto.Advantage

/-!
# Abstract Commitment Schemes

This file defines the abstract structure for commitment schemes and their
security games (correctness, hiding, binding).

## Main definitions

* `CommitmentScheme` — Structure for a commitment scheme with setup, commit, verify
* `Correct_Game` — Correctness game
* `Hiding_Game₀/₁` — Hiding games (real/ideal)
* `Binding_Game` — Binding game

## References

* [SSProve/Commitments — Com.v](https://github.com/SSProve/Commitments)
* [Kate, Zaverucha, Goldberg 2010 — §3]
-/

namespace CatCrypt.Examples.Commitments

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## Commitment Scheme Structure -/

/-- An abstract commitment scheme.

A commitment scheme consists of:
- A setup algorithm producing public parameters
- A commit algorithm producing a commitment and opening
- A verify algorithm checking validity -/
structure CommitmentScheme where
  /-- Public parameters / key type -/
  Key : Type
  /-- Message space -/
  Message : Type
  /-- Commitment type -/
  Commitment : Type
  /-- Opening / decommitment type -/
  Opening : Type
  [instFintypeKey : Fintype Key]
  [instNonemptyKey : Nonempty Key]
  [instDecEqKey : DecidableEq Key]
  [instFintypeMessage : Fintype Message]
  [instNonemptyMessage : Nonempty Message]
  [instDecEqMessage : DecidableEq Message]
  [instFintypeCommitment : Fintype Commitment]
  [instNonemptyCommitment : Nonempty Commitment]
  [instDecEqCommitment : DecidableEq Commitment]
  [instFintypeOpening : Fintype Opening]
  [instNonemptyOpening : Nonempty Opening]
  [instDecEqOpening : DecidableEq Opening]
  /-- Probabilistic setup algorithm -/
  setup : SPComp Key
  /-- Probabilistic commitment: (commitment, opening) -/
  commit : Key → Message → SPComp (Commitment × Opening)
  /-- Deterministic verification -/
  verify : Key → Message → Commitment → Opening → Bool

attribute [instance] CommitmentScheme.instFintypeKey CommitmentScheme.instNonemptyKey
  CommitmentScheme.instDecEqKey CommitmentScheme.instFintypeMessage
  CommitmentScheme.instNonemptyMessage CommitmentScheme.instDecEqMessage
  CommitmentScheme.instFintypeCommitment CommitmentScheme.instNonemptyCommitment
  CommitmentScheme.instDecEqCommitment CommitmentScheme.instFintypeOpening
  CommitmentScheme.instNonemptyOpening CommitmentScheme.instDecEqOpening

variable (S : CommitmentScheme)

/-! ## Correctness -/

/-- Correctness game: setup, commit, then verify.
    Returns `true` if verify accepts the honest commitment. -/
noncomputable def Correct_Game (m : S.Message) : SPComp Bool := do
  let k ← S.setup
  let (c, o) ← S.commit k m
  SPComp.pure (S.verify k m c o)

/-- A commitment scheme is correct if for all messages,
    the correctness game always returns true. -/
def IsCorrect : Prop :=
  ∀ m, prTrue (Correct_Game S m) Heap.empty = 1 -- Not used; we prove per-message

/-! ## Hiding -/

/-- Type of hiding adversary: chooses two messages, then distinguishes -/
structure HidingAdversary where
  /-- Choose two messages given the public key -/
  choose : S.Key → SPComp (S.Message × S.Message)
  /-- Distinguish given commitment -/
  distinguish : S.Commitment → SPComp Bool

/-- Hiding game with bit b: commit to m_b -/
noncomputable def Hiding_Game (A : HidingAdversary S) (b : Bool) : SPComp Bool := do
  let k ← S.setup
  let (m₀, m₁) ← A.choose k
  let m := if b then m₁ else m₀
  let (c, _) ← S.commit k m
  A.distinguish c

/-- Hiding advantage -/
noncomputable def Hiding_Advantage (A : HidingAdversary S) : ℝ≥0∞ :=
  Advantage (Hiding_Game S A false) (Hiding_Game S A true)

/-! ## Binding -/

/-- Type of binding adversary: given key, output two valid openings for different messages -/
abbrev BindingAdversary :=
  S.Key → SPComp (S.Message × S.Opening × S.Message × S.Opening × S.Commitment)

/-- Binding game: adversary wins if it finds two valid openings for the same
    commitment but different messages -/
noncomputable def Binding_Game (A : BindingAdversary S) : SPComp Bool := do
  let k ← S.setup
  let (m₁, o₁, m₂, o₂, c) ← A k
  SPComp.pure (decide (m₁ ≠ m₂ ∧ S.verify k m₁ c o₁ ∧ S.verify k m₂ c o₂))

/-- Binding advantage -/
noncomputable def Binding_Advantage (A : BindingAdversary S) : ℝ≥0∞ :=
  prTrue (Binding_Game S A) Heap.empty

end CatCrypt.Examples.Commitments
