/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Prob.XorBij
import CatCryptCore.Tactics

/-!
# Σ-Protocols: Completeness, SHVZK, Special Soundness, and Commitment

A Σ-protocol is a three-move public-coin proof of knowledge: the prover sends a
commitment `a`, the verifier replies with a uniform challenge `e`, the prover
answers with a response `z`, and the verifier checks `(a, e, z)`. The three
canonical properties are

* **completeness** — an honest prover with a valid witness always convinces the
  verifier;
* **special soundness** — from two accepting transcripts sharing the first
  message but with distinct challenges one *extracts* a witness;
* **special honest-verifier zero-knowledge (SHVZK)** — for a fixed challenge the
  real transcript and a witness-free *simulated* transcript are identically
  distributed.

This file ports the Schnorr/Σ example so its scope matches SSProve-Rocq's
`Schnorr.v` (perfect SHVZK + the derived commitment). We give a `SigmaProtocol`
structure, the given-challenge transcript distributions, and the three property
predicates, then instantiate the XOR-based Bool protocol `simpleSigma` and
discharge all three. Following Damgård and SSProve's `SigmaProtocol.v` §
Commitments, we derive a commitment scheme: **hiding** reduces to SHVZK (the
one-time-pad masking argument that also underlies
`Examples/Commitment.maskComm_perfect_hiding`) and **binding** reduces to special
soundness.

The SHVZK proof is a one-line bijection coupling: XOR-by-`(w ⊕ e)` is a bijection
of the sampled bit, so the real commitment `a` and the simulated response `z` are
coupled and both transcripts coincide. This is the same `liftR_uniform_bij`
coupling toolkit used by the core one-time-pad and masking-commitment examples.

## Main results

* `simpleSigma_complete` — honest executions verify.
* `simpleSigma_shvzk` — perfect SHVZK: real and simulated transcripts are equal
  as distributions (advantage `0` for every transcript distinguisher, via
  `simpleSigma_shvzk_zero_adv`).
* `simpleSigma_special_sound` — the extractor recovers the witness.
* `simpleSigma_hiding` / `simpleSigma_binding` — the derived commitment is hiding
  (from SHVZK) and binding (from special soundness).

## References

* [Damgård, *On Σ-Protocols*, §5]
* [Cramer & Damgård, *Σ-Protocols and Efficient Zero-Knowledge*]
* [Schnorr, *Efficient Signature Generation by Smart Cards*, J. Cryptology 1991]
* SSProve, `theories/Crypt/examples/Schnorr.v` and `SigmaProtocol.v`
-/

set_option autoImplicit false
-- The example's central structure is itself named `SigmaProtocol`, matching the
-- module namespace; the duplication is intentional and mirrors the mathematics.
set_option linter.dupNamespace false

namespace CatCrypt.Examples.SigmaProtocol

open CatCrypt.Core
open CatCrypt.Prob
open CatCrypt.Relational
open CatCrypt.Crypto
open scoped ENNReal

/-! ## Σ-Protocol Structure -/

/-- A Σ-protocol: types and algorithms for the three-move prover/verifier
    interaction, together with an SHVZK simulator. -/
structure SigmaProtocol where
  /-- Statements (what is proved). -/
  Statement : Type
  /-- Witnesses (the prover's secret). -/
  Witness : Type
  /-- First messages (commitments). -/
  Message : Type
  /-- Challenges (verifier coins). -/
  Challenge : Type
  /-- Responses. -/
  Response : Type
  /-- Challenges are finite (for uniform sampling). -/
  [finChallenge : Fintype Challenge]
  /-- Challenges are nonempty. -/
  [neChallenge : Nonempty Challenge]
  /-- The NP relation: `relation x w` means `w` is a witness for `x`. -/
  relation : Statement → Witness → Prop
  /-- Prover's first message. -/
  commit : Statement → Witness → SPComp Message
  /-- Prover's response to a challenge. -/
  respond : Statement → Witness → Message → Challenge → SPComp Response
  /-- Verifier's decision. -/
  verify : Statement → Message → Challenge → Response → Bool
  /-- SHVZK simulator. -/
  simulate : Statement → Challenge → SPComp (Message × Response)

attribute [instance] SigmaProtocol.finChallenge SigmaProtocol.neChallenge

/-- A transcript of a Σ-protocol run. -/
structure Transcript (sp : SigmaProtocol) where
  /-- First message (commitment). -/
  message : sp.Message
  /-- Challenge. -/
  challenge : sp.Challenge
  /-- Response. -/
  response : sp.Response

/-! ## Given-Challenge Transcript Distributions

Following SSProve's `SigmaProtocol.v`, the challenge `e` is provided as input
(the `TRANSCRIPT` procedure takes `(h, w, e)`); this is the standard SHVZK scope
and admits a one-dimensional bijection coupling. -/

/-- Real transcript for a fixed challenge: honest prover commits and responds. -/
noncomputable def realTranscript (sp : SigmaProtocol) (x : sp.Statement) (w : sp.Witness)
    (e : sp.Challenge) : SPComp (Transcript sp) := do
  let a ← sp.commit x w
  let z ← sp.respond x w a e
  return ⟨a, e, z⟩

/-- Simulated transcript for a fixed challenge: the simulator produces `(a, z)`
    without the witness. -/
noncomputable def simulatedTranscript (sp : SigmaProtocol) (x : sp.Statement)
    (e : sp.Challenge) : SPComp (Transcript sp) := do
  let (a, z) ← sp.simulate x e
  return ⟨a, e, z⟩

/-! ## Challenge-Sampling Transcript Distributions

The challenge-sampling variants draw `e` uniformly inside the distribution
rather than receiving it as input. They match the transcript distributions used
when the whole run — commitment, challenge, and response — is observed. -/

/-- Real transcript with the challenge sampled internally: honest prover commits,
    a uniform challenge is drawn, and the prover responds. -/
noncomputable def realTranscriptSampled (sp : SigmaProtocol) (x : sp.Statement)
    (w : sp.Witness) : SPComp (Transcript sp) := do
  let a ← sp.commit x w
  let e ← SPComp.sample sp.Challenge
  let z ← sp.respond x w a e
  return ⟨a, e, z⟩

/-- Simulated transcript with the challenge sampled internally: a uniform
    challenge is drawn and the simulator produces `(a, z)` without the witness. -/
noncomputable def simulatedTranscriptSampled (sp : SigmaProtocol) (x : sp.Statement) :
    SPComp (Transcript sp) := do
  let e ← SPComp.sample sp.Challenge
  let (a, z) ← sp.simulate x e
  return ⟨a, e, z⟩

/-! ## Property Predicates -/

/-- Completeness: honest transcripts verify. -/
def Completeness (sp : SigmaProtocol) : Prop :=
  ∀ x w, sp.relation x w → ∀ a e z, sp.verify x a e z = true

/-- Perfect SHVZK: for any valid statement/witness and any fixed challenge, the
    real and simulated transcript distributions are equal — coupled by `eqPre`
    to `eqPost`, hence indistinguishable to every transcript distinguisher. -/
def SHVZK (sp : SigmaProtocol) : Prop :=
  ∀ x w e, sp.relation x w →
    rHoare eqPre (realTranscript sp x w e) (simulatedTranscript sp x e) eqPost

/-- Two accepting transcripts sharing the first message but with distinct
    challenges — the input to a special-soundness extractor. -/
structure TwoTranscripts (sp : SigmaProtocol) (x : sp.Statement) where
  /-- Shared first message. -/
  message : sp.Message
  /-- First challenge. -/
  challenge₁ : sp.Challenge
  /-- First response. -/
  response₁ : sp.Response
  /-- Second challenge. -/
  challenge₂ : sp.Challenge
  /-- Second response. -/
  response₂ : sp.Response
  /-- First transcript accepts. -/
  accept₁ : sp.verify x message challenge₁ response₁ = true
  /-- Second transcript accepts. -/
  accept₂ : sp.verify x message challenge₂ response₂ = true
  /-- Challenges differ. -/
  diff : challenge₁ ≠ challenge₂

/-- Special soundness: an extractor turns any `TwoTranscripts` into a witness. -/
def SpecialSoundness (sp : SigmaProtocol) : Prop :=
  ∃ extractor : ∀ x : sp.Statement, TwoTranscripts sp x → sp.Witness,
    ∀ x (tt : TwoTranscripts sp x), sp.relation x (extractor x tt)

/-! ## XOR-Based Σ-Protocol over `Bool`

The demonstration protocol: everything is a bit, the relation is `x = w`, the
response masks the commitment by `w ⊕ e`, and the simulator masks a fresh
response instead. -/

/-- The XOR bijection carrying SHVZK: for fixed `w, e`, the map `a ↦ a ⊕ w ⊕ e`
    couples the real commitment with the simulated response. -/
def xorTransformBij (w e : Bool) : Bool ≃ Bool where
  toFun a := xor (xor a w) e
  invFun z := xor (xor z e) w
  left_inv a := by cases a <;> cases w <;> cases e <;> rfl
  right_inv z := by cases z <;> cases w <;> cases e <;> rfl

@[simp]
theorem xorTransformBij_apply (w e a : Bool) :
    xorTransformBij w e a = xor (xor a w) e := rfl

/-- The XOR-based Σ-protocol over `Bool`. -/
noncomputable def simpleSigma : SigmaProtocol where
  Statement := Bool
  Witness := Bool
  Message := Bool
  Challenge := Bool
  Response := Bool
  relation := fun x w => x = w
  commit := fun _ _ => SPComp.sample Bool
  respond := fun _ w a e => SPComp.pure (xor (xor a w) e)
  verify := fun x a e z => (xor a z) == (xor x e)
  simulate := fun x e => do
    let z ← SPComp.sample Bool
    SPComp.pure (xor z (xor x e), z)

/-! ## Completeness -/

/-- Completeness: an honest transcript `(a, e, a ⊕ w ⊕ e)` verifies. -/
theorem simpleSigma_complete (x w : Bool) (hrel : simpleSigma.relation x w) (a e : Bool) :
    let z := xor (xor a w) e
    simpleSigma.verify x a e z = true := by
  simp_all [simpleSigma]

/-! ## SHVZK -/

/-- **Perfect SHVZK for `simpleSigma`.** The bijection `xorTransformBij x e`
    couples the real sampled commitment `a` with the simulated sampled response
    `z = a ⊕ x ⊕ e`; the simulated message `z ⊕ x ⊕ e` collapses back to `a`, so
    both runs yield the identical transcript. The whole argument is one
    `liftR_bind (liftR_uniform_bij …)` coupling. -/
theorem simpleSigma_shvzk : SHVZK simpleSigma := by
  rintro x w e rfl
  unfold realTranscript simulatedTranscript
  simp only [simpleSigma, ssprove_simpl, SPComp.monad_pure_eq]
  ssprove_couple_bij (xorTransformBij x e)

/-- Perfect SHVZK, advantage form: no distinguisher separates the real from the
    simulated transcript. -/
theorem simpleSigma_shvzk_zero_adv (x e : Bool) (A : Transcript simpleSigma → SPComp Bool) :
    AdvantageA (realTranscript simpleSigma x x e) (simulatedTranscript simpleSigma x e) A = 0 :=
  advantage_zero_of_rHoare _ _ (simpleSigma_shvzk x x e rfl) A

/-! ## Special Soundness -/

/-- Extractor for `simpleSigma`: from `(a, e₁, z₁)` accepting, `a ⊕ z₁ = x ⊕ e₁`,
    so `x = a ⊕ z₁ ⊕ e₁`. -/
def simpleSigmaExtractor (x : Bool) (tt : TwoTranscripts simpleSigma x) : Bool :=
  xor (xor tt.message tt.response₁) tt.challenge₁

/-- **Special soundness for `simpleSigma`.** -/
theorem simpleSigma_special_sound : SpecialSoundness simpleSigma := by
  refine ⟨simpleSigmaExtractor, fun x tt => ?_⟩
  have := tt.accept₁
  simp_all [simpleSigma, simpleSigmaExtractor]

/-! ## Derived Commitment Scheme

The Σ-protocol's first message is a commitment to the challenge, with the
response as opening (Damgård §5, SSProve `SigmaProtocol.v` § Commitments). -/

/-- Hiding: the real and simulated commitment transcripts are equidistributed —
    a direct instance of SHVZK. The masking here is exactly the one-time pad that
    makes `Examples/Commitment.maskComm` perfectly hiding. -/
theorem simpleSigma_hiding (x e : Bool) :
    rHoare eqPre (realTranscript simpleSigma x x e) (simulatedTranscript simpleSigma x e) eqPost :=
  simpleSigma_shvzk x x e rfl

/-- Two openings of a single commitment under different challenges. -/
structure DoubleOpening (sp : SigmaProtocol) (x : sp.Statement) where
  /-- The shared commitment. -/
  commitment : sp.Message
  /-- First challenge. -/
  challenge₁ : sp.Challenge
  /-- First response. -/
  response₁ : sp.Response
  /-- Second challenge. -/
  challenge₂ : sp.Challenge
  /-- Second response. -/
  response₂ : sp.Response
  /-- Challenges differ. -/
  diff : challenge₁ ≠ challenge₂
  /-- First opening verifies. -/
  verify₁ : sp.verify x commitment challenge₁ response₁ = true
  /-- Second opening verifies. -/
  verify₂ : sp.verify x commitment challenge₂ response₂ = true

/-- A double opening is exactly the input to the special-soundness extractor. -/
def DoubleOpening.toTwoTranscripts {sp : SigmaProtocol} {x : sp.Statement}
    (dop : DoubleOpening sp x) : TwoTranscripts sp x where
  message := dop.commitment
  challenge₁ := dop.challenge₁
  response₁ := dop.response₁
  challenge₂ := dop.challenge₂
  response₂ := dop.response₂
  accept₁ := dop.verify₁
  accept₂ := dop.verify₂
  diff := dop.diff

/-- **Binding from special soundness.** An adversary who double-opens a
    commitment yields a witness, so breaking binding solves the hard instance. -/
theorem commitment_binding (sp : SigmaProtocol) (hSS : SpecialSoundness sp)
    (x : sp.Statement) (dop : DoubleOpening sp x) : ∃ w, sp.relation x w := by
  exact ⟨_, hSS.choose_spec x dop.toTwoTranscripts⟩

/-- **Binding for the `simpleSigma` commitment.** -/
theorem simpleSigma_binding (x : Bool) (dop : DoubleOpening simpleSigma x) :
    ∃ w, simpleSigma.relation x w :=
  commitment_binding simpleSigma simpleSigma_special_sound x dop

end CatCrypt.Examples.SigmaProtocol
