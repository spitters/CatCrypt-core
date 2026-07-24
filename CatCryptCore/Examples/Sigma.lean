/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Package
import CatCryptCore.Invariant
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Relational.Rules
import CatCryptCore.Tactics.Basic
import CatCryptCore.Tactics.Sim

/-!
# Sigma Protocol Example

This file demonstrates Sigma protocols formalized in CatCrypt-Lean4.

## Overview

A Sigma protocol is a three-move public-coin interactive proof system:
1. Prover sends commitment (message)
2. Verifier sends random challenge
3. Prover sends response
4. Verifier accepts/rejects

## Properties

* **Completeness**: Honest prover with valid witness is always accepted
* **Special Soundness**: From two accepting transcripts with same commitment
  but different challenges, one can extract a valid witness
* **Special Honest-Verifier Zero-Knowledge (SHVZK)**: A simulator can produce
  transcripts indistinguishable from real ones given only the statement and challenge

## Implementation

We use a simplified model over Bool types (like PRF.lean) to demonstrate the
proof techniques. The key insight for SHVZK is that if the simulator samples
the challenge first and then computes (message, response) via a bijection,
it produces the same distribution as the real protocol.

## References

* [Damgard, On Sigma Protocols]
* [Cramer & Damgard, Sigma Protocols and Efficient Zero-Knowledge]
-/

namespace CatCrypt.Examples.Sigma

open CatCrypt.Core
open CatCrypt.Package
open CatCrypt.Prob
open CatCrypt.Relational
open CatCrypt.Invariant
open CatCrypt.Crypto

/-! ## Type Definitions -/

/-- Use Bool as simple finite type for demonstration -/
abbrev Value := Bool

instance : Fintype Value := inferInstance
instance : Nonempty Value := ⟨false⟩
instance : DecidableEq Value := inferInstance

/-! ## Sigma Protocol Structure -/

/-- A Sigma protocol consists of types and algorithms for the three-move
    interaction between prover and verifier. -/
structure SigmaProtocol where
  /-- Type of statements (what we're proving) -/
  Statement : Type
  /-- Type of witnesses (secret known to prover) -/
  Witness : Type
  /-- Type of first message (commitment) -/
  Message : Type
  /-- Type of challenge (from verifier) -/
  Challenge : Type
  /-- Type of response -/
  Response : Type
  /-- Challenge type is finite (for uniform sampling) -/
  [finChallenge : Fintype Challenge]
  /-- Challenge type is nonempty -/
  [neChallenge : Nonempty Challenge]
  /-- The NP relation: R(x, w) means w is a valid witness for x -/
  relation : Statement → Witness → Prop
  /-- Prover's first message (commitment) -/
  commit : Statement → Witness → SPComp Message
  /-- Prover's response to a challenge -/
  respond : Statement → Witness → Message → Challenge → SPComp Response
  /-- Verifier's check -/
  verify : Statement → Message → Challenge → Response → Bool
  /-- Simulator for SHVZK -/
  simulate : Statement → Challenge → SPComp (Message × Response)

attribute [instance] SigmaProtocol.finChallenge SigmaProtocol.neChallenge

/-! ## Transcript Type -/

/-- A transcript of a Sigma protocol execution -/
structure Transcript (sp : SigmaProtocol) where
  message : sp.Message
  challenge : sp.Challenge
  response : sp.Response

/-! ## Protocol Computations -/

/-- Real protocol execution: prover with witness generates transcript -/
noncomputable def realTranscript (sp : SigmaProtocol) (x : sp.Statement) (w : sp.Witness) :
    SPComp (Transcript sp) := do
  let a ← sp.commit x w
  let e ← SPComp.sample sp.Challenge
  let z ← sp.respond x w a e
  return ⟨a, e, z⟩

/-- Simulated transcript: simulator generates transcript given challenge -/
noncomputable def simulatedTranscript (sp : SigmaProtocol) (x : sp.Statement) :
    SPComp (Transcript sp) := do
  let e ← SPComp.sample sp.Challenge
  let (a, z) ← sp.simulate x e
  return ⟨a, e, z⟩

/-! ## Protocol Computations with Given Challenge (Rocq style)

In the standard cryptographic definition of SHVZK, the challenge is provided as input
rather than sampled internally. This matches Rocq's CatCrypt formalization where
`chInput = (h, w, e)` includes the challenge. This allows a simpler 1D bijection
coupling proof. -/

/-- Real protocol with given challenge: prover generates transcript for fixed challenge -/
noncomputable def realTranscriptGiven (sp : SigmaProtocol) (x : sp.Statement) (w : sp.Witness)
    (e : sp.Challenge) : SPComp (Transcript sp) := do
  let a ← sp.commit x w
  let z ← sp.respond x w a e
  return ⟨a, e, z⟩

/-- Simulated transcript with given challenge -/
noncomputable def simulatedTranscriptGiven (sp : SigmaProtocol) (x : sp.Statement)
    (e : sp.Challenge) : SPComp (Transcript sp) := do
  let (a, z) ← sp.simulate x e
  return ⟨a, e, z⟩

/-! ## Completeness Property -/

/-- Completeness: honest execution with valid witness always verifies -/
def Completeness (sp : SigmaProtocol) : Prop :=
  ∀ x w, sp.relation x w →
    ∀ a e z, sp.verify x a e z = true

/-! ## Special Soundness Property -/

/-- Two accepting transcripts with same message but different challenges -/
structure TwoTranscripts (sp : SigmaProtocol) (x : sp.Statement) where
  message : sp.Message
  challenge1 : sp.Challenge
  response1 : sp.Response
  challenge2 : sp.Challenge
  response2 : sp.Response
  accept1 : sp.verify x message challenge1 response1 = true
  accept2 : sp.verify x message challenge2 response2 = true
  diff : challenge1 ≠ challenge2

/-- Special soundness: from two accepting transcripts with same commitment
    but different challenges, extract a valid witness -/
def SpecialSoundness (sp : SigmaProtocol) : Prop :=
  ∃ extractor : ∀ x : sp.Statement, TwoTranscripts sp x → sp.Witness,
    ∀ x (tt : TwoTranscripts sp x), sp.relation x (extractor x tt)

/-! ## SHVZK Property -/

/-- Special Honest-Verifier Zero-Knowledge (given challenge version):
    For any given challenge, real and simulated transcripts have the same distribution.

    This is the standard cryptographic definition where the challenge is provided
    as input (matching Rocq's CatCrypt formalization). This formulation allows
    a simple 1D bijection coupling proof. -/
def SHVZK_given (sp : SigmaProtocol) : Prop :=
  ∀ x w e, sp.relation x w →
    rHoare
      (fun _ _ => True)
      (realTranscriptGiven sp x w e)
      (simulatedTranscriptGiven sp x e)
      (fun t₁ _ t₂ _ => t₁ = t₂)

/-- Special Honest-Verifier Zero-Knowledge: real and simulated transcripts
    have the same distribution for any statement with a valid witness.

    This is formalized using rHoare: for any precondition, the real and
    simulated computations produce outputs that are equal (same transcript). -/
def SHVZK (sp : SigmaProtocol) : Prop :=
  ∀ x w, sp.relation x w →
    rHoare
      (fun _ _ => True)
      (realTranscript sp x w)
      (simulatedTranscript sp x)
      (fun t₁ _ t₂ _ => t₁ = t₂)

/-! ## Simple Example: XOR-based Protocol over Bool -/

/-- A simple Sigma protocol where the statement is the XOR of message and response,
    and the witness is either true or false.

    Statement: x
    Witness: w such that x = (witness property)
    Protocol:
    - Commit: sample random message a
    - Challenge: e (random Bool)
    - Response: z = xor a (xor w e)
    - Verify: check that xor a z = xor w e... (simplified)

    For simplicity, we use a trivial protocol where everything is in Bool. -/
noncomputable def simpleSigma : SigmaProtocol where
  Statement := Bool
  Witness := Bool
  Message := Bool
  Challenge := Bool
  Response := Bool
  relation := fun x w => x = w  -- trivial relation for demo
  commit := fun _ _ => SPComp.sample Bool
  respond := fun _ w a e => SPComp.pure (xor (xor a w) e)
  verify := fun x a e z => (xor a z) == (xor x e)
  simulate := fun x e => do
    let z ← SPComp.sample Bool
    let a := xor z (xor x e)
    return (a, z)

/-! ## Bijection for SHVZK Proof

The key bijection for SHVZK relates sampled values directly:

- Real: sample a, compute z = xor (xor a w) e
- Simulated: sample z, compute a = xor z (xor x e)

When x = w:
- From real (a, z): z = xor (xor a w) e
- The bijection f : a ↦ z = xor (xor a w) e is an equiv on Bool

If we show uniform(a).bind(a ↦ pure(a, f(a))) = uniform(z).bind(z ↦ pure(f⁻¹(z), z)),
then the transcripts have the same distribution.
-/

/-- XOR-based bijection: for fixed w and e, mapping a to z -/
def xorTransformBij (w e : Bool) : Bool ≃ Bool where
  toFun a := xor (xor a w) e
  invFun z := xor (xor z e) w
  left_inv a := by cases a <;> cases w <;> cases e <;> rfl
  right_inv z := by cases z <;> cases w <;> cases e <;> rfl

/-- The forward map of `xorTransformBij w e` sends `a` to `a ⊕ w ⊕ e`. -/
@[simp]
theorem xorTransformBij_apply (w e a : Bool) :
    xorTransformBij w e a = xor (xor a w) e := rfl

/-- The inverse map of `xorTransformBij w e` sends `z` to `z ⊕ e ⊕ w`. -/
@[simp]
theorem xorTransformBij_symm_apply (w e z : Bool) :
    (xorTransformBij w e).symm z = xor (xor z e) w := rfl

/-- 2D bijection for Sigma protocol SHVZK:
    Maps (a, e) from Real protocol to (e', z) from Simulation
    where e' = e (challenges match) and z = xor (xor a w) e (responses match).
    Then Sim's computed message = xor z (xor w e') = a = Real's message. -/
def sigmaBij (w : Bool) : Bool × Bool ≃ Bool × Bool where
  toFun := fun (a, e) => (e, xor (xor a w) e)
  invFun := fun (e', z) => (xor (xor z e') w, e')
  left_inv := fun (a, e) => by cases a <;> cases w <;> cases e <;> rfl
  right_inv := fun (e', z) => by cases e' <;> cases w <;> cases z <;> rfl

/-- The first component of `sigmaBij w (a, e)` is the challenge `e`. -/
@[simp]
theorem sigmaBij_fst (w a e : Bool) : (sigmaBij w (a, e)).1 = e := rfl

/-- The second component of `sigmaBij w (a, e)` is the response `a ⊕ w ⊕ e`. -/
@[simp]
theorem sigmaBij_snd (w a e : Bool) : (sigmaBij w (a, e)).2 = xor (xor a w) e := rfl

/-! ## Completeness Proof for simpleSigma -/

/-- Completeness for simpleSigma: honest executions always verify.

    Note: The generic `Completeness` definition above is too strong as it
    requires verify to succeed for ALL z values. The correct formulation
    is that verify succeeds for z produced by the honest `respond` function.
    This theorem captures the correct completeness property. -/
theorem simpleSigma_complete' (x w : Bool) (hrel : simpleSigma.relation x w)
    (a e : Bool) :
    let z := xor (xor a w) e
    simpleSigma.verify x a e z = true := by
  simp_all [simpleSigma]

/-! ## SHVZK Proof for simpleSigma -/

/-- SHVZK for simpleSigma with given challenge: the core bijection coupling proof.

    This follows Rocq's CatCrypt approach where the challenge `e` is provided as input.
    The bijection `xorTransformBij w e : a ↦ z = a ⊕ w ⊕ e` couples:
    - Real's sampled commitment `a`
    - Sim's sampled response `z`

    Since `a' = z ⊕ w ⊕ e = (a ⊕ w ⊕ e) ⊕ w ⊕ e = a`, both produce the same
    transcript. -/
theorem simpleSigma_shvzk_given : SHVZK_given simpleSigma := by
  intro x w e hrel
  simp only [simpleSigma] at hrel
  subst hrel
  unfold realTranscriptGiven simulatedTranscriptGiven simpleSigma
  ssprove_code_simpl
  ssprove_couple_bij (xorTransformBij x e)

/-- SHVZK for `simpleSigma` with the challenge sampled internally rather than
    supplied as input.

    This extends the standard SHVZK definition used in Rocq's CatCrypt
    (`SigmaProtocol.v:163-170`), where the challenge is part of the input
    `(h, w, e)`. The `SHVZK_given` theorem above matches that input-challenge
    formulation; this variant samples the challenge inside the protocol. -/
theorem simpleSigma_shvzk : SHVZK simpleSigma := by
  intro x w hrel
  simp only [simpleSigma] at hrel
  subst hrel
  unfold realTranscript simulatedTranscript simpleSigma
  ssprove_code_simpl
  apply rHoare_swap_lhs (SPComp.swap_sample_sample Bool Bool _ _)
  apply rHoare_same_step; intro e
  ssprove_couple_bij (xorTransformBij x e)

/-! ## Special Soundness for simpleSigma -/

/-- The extractor for simpleSigma: given two transcripts with same a, different e,
    extract the witness.

    From two accepting transcripts:
    - (a, e₁, z₁) with xor a z₁ = xor x e₁
    - (a, e₂, z₂) with xor a z₂ = xor x e₂

    We can compute:
    xor (xor a z₁) (xor a z₂) = xor (xor x e₁) (xor x e₂)
    xor z₁ z₂ = xor e₁ e₂  (by XOR properties)

    And from xor a z₁ = xor x e₁:
    x = xor (xor a z₁) e₁

    So the extractor returns: xor (xor a z₁) e₁ -/
def simpleSigmaExtractor (x : Bool) (tt : TwoTranscripts simpleSigma x) : Bool :=
  xor (xor tt.message tt.response1) tt.challenge1

/-- `simpleSigma` satisfies special soundness: `simpleSigmaExtractor` recovers a
    valid witness from any two accepting transcripts sharing a commitment. -/
theorem simpleSigma_special_sound : SpecialSoundness simpleSigma := by
  use simpleSigmaExtractor
  intro x tt
  -- Need: simpleSigma.relation x (simpleSigmaExtractor x tt)
  -- i.e., x = xor (xor tt.message tt.response1) tt.challenge1
  have h1 : xor tt.message tt.response1 = xor x tt.challenge1 :=
    beq_iff_eq.mp (by simpa [simpleSigma] using tt.accept1)
  simp only [simpleSigma, simpleSigmaExtractor, h1]
  cases x <;> cases tt.challenge1 <;> rfl

end CatCrypt.Examples.Sigma
