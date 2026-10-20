/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.Sigma

/-!
# Sigma Protocol Compositions: AND and OR

Generic constructions composing two Sigma protocols `Σ₁` for `R₁` and `Σ₂` for `R₂`.

## Sigma-AND

`sigmaAND` proves `R₁ ∧ R₂`: both protocols run in parallel on one challenge.
It is complete (`sigmaAND_completeness`), special sound
(`sigmaAND_special_soundness`) and special honest-verifier zero-knowledge
(`sigmaAND_shvzk_given`) when its components are. Completeness and SHVZK assume
that the commitment of `Σ₂` does not use the heap (`SPComp.IsPure`), since the
second commitment runs between the first commitment and the first response.

## Sigma-OR (Cramer–Damgård–Schoenmakers)

`sigmaOR` proves `R₁ ∨ R₂` for challenges in a finite additive group `G`, with
`ι₁ : G ≃ Σ₁.Challenge` and `ι₂ : G ≃ Σ₂.Challenge`. The prover holding a witness
for one side samples the challenge of the other side, simulates that side's
transcript, and on the verifier's challenge `c` answers its own side at the
remaining share, so that the two shares sum to `c`. The response carries the
share `c₁` of the first side; the verifier checks the first side at `c₁` and the
second at `c - c₁`.

The prover keeps the simulated share and response between its two moves, so
`sigmaOR` is a `SigmaProtocolS`. Its properties are stated by
`CompletenessS` and `SHVZK_givenS`, the counterparts of `Completeness` and
`SHVZK_given` for protocols with prover state, and by `SpecialSoundness` of
`SigmaProtocolS.toSigmaProtocol`, whose verifier is that of `sigmaOR`.

* `sigmaOR_completeness` — from completeness of both components and simulators
  whose transcripts verify
* `sigmaOR_special_soundness` — from special soundness of both components: two
  accepting transcripts with different challenges differ in the share of at
  least one side
* `sigmaOR_shvzk_given` — from SHVZK of both components and heap-free simulators

## References

* [Cramer, Damgård & Schoenmakers, Proofs of Partial Knowledge, 1994]
* [Damgård, On Sigma Protocols, §6]
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.SigmaCompositions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Examples.Sigma
open CatCrypt.Relational
open scoped ENNReal

/-! ## Relational helpers -/

/-- A computation that does not use the heap is related to itself on equal outputs,
from any pair of heaps. -/
theorem rHoare_eq_self_of_isPure {α : Type} {c : SPComp α} (hc : SPComp.IsPure c) :
    rHoare (fun _ _ => True) c c (fun a₁ _ a₂ _ => a₁ = a₂) := by
  obtain ⟨d, hd⟩ := hc
  intro h₁ h₂ _
  rw [hd h₁, hd h₂]
  exact liftR_bind (liftR_refl d) fun a b hab => liftR_pure (by exact hab)

/-- SHVZK at a challenge, followed by a deterministic map of the transcript: the
mapped real and simulated transcripts are equal in distribution. -/
theorem shvzk_given_map {sp : SigmaProtocol} (hzk : SHVZK_given sp) {x : sp.Statement}
    {w : sp.Witness} (hrel : sp.relation x w) (e : sp.Challenge) {β : Type}
    (g : Transcript sp → β) :
    rHoare (fun _ _ => True)
      (SPComp.bind (realTranscriptGiven sp x w e) fun t => SPComp.pure (g t))
      (SPComp.bind (simulatedTranscriptGiven sp x e) fun t => SPComp.pure (g t))
      (fun b₁ _ b₂ _ => b₁ = b₂) :=
  rHoare_bind (hzk x w e hrel) fun _ _ => rHoare_ret fun _ _ h => congrArg g h

/-! ## Sigma-AND Construction -/

/-- Sigma-AND protocol: run both protocols in parallel on one challenge.

- Statement = (Σ₁.Statement, Σ₂.Statement)
- Witness = (Σ₁.Witness, Σ₂.Witness)
- Message = (Σ₁.Message, Σ₂.Message)
- Challenge = Σ₁.Challenge, transported to Σ₂.Challenge along `hChallenge`
- Response = (Σ₁.Response, Σ₂.Response) -/
noncomputable def sigmaAND (sp₁ sp₂ : SigmaProtocol)
    (hChallenge : sp₁.Challenge = sp₂.Challenge) : SigmaProtocol where
  Statement := sp₁.Statement × sp₂.Statement
  Witness := sp₁.Witness × sp₂.Witness
  Message := sp₁.Message × sp₂.Message
  Challenge := sp₁.Challenge
  Response := sp₁.Response × sp₂.Response
  finChallenge := sp₁.finChallenge
  neChallenge := sp₁.neChallenge
  relation := fun x w => sp₁.relation x.1 w.1 ∧ sp₂.relation x.2 w.2
  commit := fun x w => do
    let a₁ ← sp₁.commit x.1 w.1
    let a₂ ← sp₂.commit x.2 w.2
    return (a₁, a₂)
  respond := fun x w a e => do
    let z₁ ← sp₁.respond x.1 w.1 a.1 e
    let z₂ ← sp₂.respond x.2 w.2 a.2 (hChallenge ▸ e)
    return (z₁, z₂)
  verify := fun x a e z =>
    sp₁.verify x.1 a.1 e z.1 && sp₂.verify x.2 a.2 (hChallenge ▸ e) z.2
  simulate := fun x e => do
    let t₁ ← sp₁.simulate x.1 e
    let t₂ ← sp₂.simulate x.2 (hChallenge ▸ e)
    return ((t₁.1, t₂.1), (t₁.2, t₂.2))

/-- Verification of Sigma-AND: if both component transcripts verify,
    the AND transcript verifies. -/
theorem sigmaAND_verify (sp₁ sp₂ : SigmaProtocol)
    (hChallenge : sp₁.Challenge = sp₂.Challenge)
    {x₁ : sp₁.Statement} {x₂ : sp₂.Statement}
    {a₁ : sp₁.Message} {a₂ : sp₂.Message}
    {e : sp₁.Challenge} {z₁ : sp₁.Response} {z₂ : sp₂.Response}
    (hv₁ : sp₁.verify x₁ a₁ e z₁ = true)
    (hv₂ : sp₂.verify x₂ a₂ (hChallenge ▸ e) z₂ = true) :
    (sigmaAND sp₁ sp₂ hChallenge).verify (x₁, x₂) (a₁, a₂) e (z₁, z₂) = true := by
  simp only [sigmaAND, Bool.and_eq_true]
  exact ⟨hv₁, hv₂⟩

/-- The honest run of Sigma-AND at challenge `e` is the honest run of `Σ₁` followed
by the honest run of `Σ₂`, when the commitment of `Σ₂` does not use the heap. -/
theorem sigmaAND_realTranscriptGiven (sp₁ sp₂ : SigmaProtocol)
    (hChallenge : sp₁.Challenge = sp₂.Challenge)
    (hpure : ∀ x w, SPComp.IsPure (sp₂.commit x w))
    (x : sp₁.Statement × sp₂.Statement) (w : sp₁.Witness × sp₂.Witness)
    (e : sp₁.Challenge) :
    realTranscriptGiven (sigmaAND sp₁ sp₂ hChallenge) x w e =
      SPComp.bind (realTranscriptGiven sp₁ x.1 w.1 e) fun t₁ =>
        SPComp.bind (realTranscriptGiven sp₂ x.2 w.2 (hChallenge ▸ e)) fun t₂ =>
          SPComp.pure (⟨(t₁.message, t₂.message), e, (t₁.response, t₂.response)⟩ :
            Transcript (sigmaAND sp₁ sp₂ hChallenge)) := by
  simp only [realTranscriptGiven, sigmaAND, SPComp.monad_bind_eq, SPComp.monad_pure_eq,
    SPComp.bind_assoc, SPComp.pure_bind]
  congr 1
  funext a₁
  exact SPComp.isPure_bind_comm_left _ _ _ (hpure _ _)

/-- The simulated run of Sigma-AND at challenge `e` is the simulated run of `Σ₁`
followed by the simulated run of `Σ₂`. -/
theorem sigmaAND_simulatedTranscriptGiven (sp₁ sp₂ : SigmaProtocol)
    (hChallenge : sp₁.Challenge = sp₂.Challenge)
    (x : sp₁.Statement × sp₂.Statement) (e : sp₁.Challenge) :
    simulatedTranscriptGiven (sigmaAND sp₁ sp₂ hChallenge) x e =
      SPComp.bind (simulatedTranscriptGiven sp₁ x.1 e) fun t₁ =>
        SPComp.bind (simulatedTranscriptGiven sp₂ x.2 (hChallenge ▸ e)) fun t₂ =>
          SPComp.pure (⟨(t₁.message, t₂.message), e, (t₁.response, t₂.response)⟩ :
            Transcript (sigmaAND sp₁ sp₂ hChallenge)) := by
  simp only [simulatedTranscriptGiven, sigmaAND, SPComp.monad_bind_eq, SPComp.monad_pure_eq,
    SPComp.bind_assoc, SPComp.pure_bind]

/-- Completeness of Sigma-AND, for components that are complete and a second
component whose commitment does not use the heap. -/
theorem sigmaAND_completeness (sp₁ sp₂ : SigmaProtocol)
    (hChallenge : sp₁.Challenge = sp₂.Challenge)
    (hc₁ : Completeness sp₁) (hc₂ : Completeness sp₂)
    (hpure : ∀ x w, SPComp.IsPure (sp₂.commit x w)) :
    Completeness (sigmaAND sp₁ sp₂ hChallenge) := by
  intro x w e hrel
  rw [sigmaAND_realTranscriptGiven sp₁ sp₂ hChallenge hpure x w e]
  refine CatCrypt.Unary.pHoare_bind (hc₁ x.1 w.1 e hrel.1) fun t₁ => ?_
  refine CatCrypt.Unary.pHoare_bind
    (Mid := fun t₂ _ => sp₁.verify x.1 t₁.message e t₁.response = true ∧
      sp₂.verify x.2 t₂.message (hChallenge ▸ e) t₂.response = true) ?_ fun t₂ => ?_
  · intro h₀ hv₁ a h' hs
    exact ⟨hv₁, hc₂ x.2 w.2 _ hrel.2 h₀ trivial a h' hs⟩
  · exact CatCrypt.Unary.pHoare_ret fun _ hv => by
      simp only [sigmaAND, Bool.and_eq_true]
      exact hv

/-- Special soundness of Sigma-AND: extract both witnesses independently. -/
theorem sigmaAND_special_soundness (sp₁ sp₂ : SigmaProtocol)
    (hChallenge : sp₁.Challenge = sp₂.Challenge)
    (hSS₁ : SpecialSoundness sp₁)
    (hSS₂ : SpecialSoundness sp₂) :
    SpecialSoundness (sigmaAND sp₁ sp₂ hChallenge) := by
  obtain ⟨ext₁, hext₁⟩ := hSS₁
  obtain ⟨ext₂, hext₂⟩ := hSS₂
  refine ⟨fun x tt => ?_, fun x tt => ?_⟩
  · exact (ext₁ x.1 {
      message := tt.message.1
      challenge1 := tt.challenge1
      response1 := tt.response1.1
      challenge2 := tt.challenge2
      response2 := tt.response2.1
      accept1 := by
        have := tt.accept1
        simp only [sigmaAND, Bool.and_eq_true] at this
        exact this.1
      accept2 := by
        have := tt.accept2
        simp only [sigmaAND, Bool.and_eq_true] at this
        exact this.1
      diff := tt.diff
    }, ext₂ x.2 {
      message := tt.message.2
      challenge1 := hChallenge ▸ tt.challenge1
      response1 := tt.response1.2
      challenge2 := hChallenge ▸ tt.challenge2
      response2 := tt.response2.2
      accept1 := by
        have := tt.accept1
        simp only [sigmaAND, Bool.and_eq_true] at this
        exact this.2
      accept2 := by
        have := tt.accept2
        simp only [sigmaAND, Bool.and_eq_true] at this
        exact this.2
      diff := by
        intro heq
        apply tt.diff
        have hinj : ∀ {A B : Type} (h : A = B) {x y : A}, (h ▸ x = h ▸ y) → x = y := by
          intro A B h; subst h; exact id
        exact hinj hChallenge heq
    })
  · exact ⟨hext₁ x.1 _, hext₂ x.2 _⟩

/-- SHVZK of Sigma-AND, for components with SHVZK and a second component whose
commitment does not use the heap. -/
theorem sigmaAND_shvzk_given (sp₁ sp₂ : SigmaProtocol)
    (hChallenge : sp₁.Challenge = sp₂.Challenge)
    (hz₁ : SHVZK_given sp₁) (hz₂ : SHVZK_given sp₂)
    (hpure : ∀ x w, SPComp.IsPure (sp₂.commit x w)) :
    SHVZK_given (sigmaAND sp₁ sp₂ hChallenge) := by
  intro x w e hrel
  rw [sigmaAND_realTranscriptGiven sp₁ sp₂ hChallenge hpure x w e,
    sigmaAND_simulatedTranscriptGiven sp₁ sp₂ hChallenge x e]
  refine rHoare_bind (hz₁ x.1 w.1 e hrel.1) fun t₁ t₁' => ?_
  intro h₁ h₂ (heq : t₁ = t₁')
  subst heq
  exact shvzk_given_map hz₂ hrel.2 _ _ h₁ h₂ trivial

/-! ## Predicates for protocols with prover state -/

/-- The honest run of a protocol with prover state at a given challenge, as the
triple of first message, challenge and response. -/
noncomputable def realTranscriptGivenS (sps : SigmaProtocolS) (x : sps.Statement)
    (w : sps.Witness) (e : sps.Challenge) :
    SPComp (sps.Message × sps.Challenge × sps.Response) :=
  SPComp.bind (sps.commit x w) fun p =>
    SPComp.bind (sps.respond x w p.2 p.1 e) fun z => SPComp.pure (p.1, e, z)

/-- The simulated run of a protocol with prover state at a given challenge. -/
noncomputable def simulatedTranscriptGivenS (sps : SigmaProtocolS) (x : sps.Statement)
    (e : sps.Challenge) : SPComp (sps.Message × sps.Challenge × sps.Response) :=
  SPComp.bind (sps.simulate x e) fun t => SPComp.pure (t.1, e, t.2)

/-- Completeness of a protocol with prover state: every honest transcript at every
challenge verifies. -/
def CompletenessS (sps : SigmaProtocolS) : Prop :=
  ∀ x w e, sps.relation x w →
    CatCrypt.Unary.pHoare (fun _ => True) (realTranscriptGivenS sps x w e)
      (fun t _ => sps.verify x t.1 e t.2.2 = true)

/-- SHVZK of a protocol with prover state: at every challenge, the honest and the
simulated transcripts are equal in distribution. -/
def SHVZK_givenS (sps : SigmaProtocolS) : Prop :=
  ∀ x w e, sps.relation x w →
    rHoare (fun _ _ => True) (realTranscriptGivenS sps x w e)
      (simulatedTranscriptGivenS sps x e) (fun t₁ _ t₂ _ => t₁ = t₂)

/-- The simulator of a protocol produces accepting transcripts, for every statement
and challenge. The OR prover relies on it for the side it has no witness for. -/
def SimulatorAccepts (sp : SigmaProtocol) : Prop :=
  ∀ x e, CatCrypt.Unary.pHoare (fun _ => True) (sp.simulate x e)
    (fun t _ => sp.verify x t.1 e t.2 = true)

/-! ## Sigma-OR Construction (Cramer–Damgård–Schoenmakers) -/

section OR

variable {G : Type} [AddCommGroup G] [Fintype G] [Nonempty G]

/-- Sigma-OR protocol for challenges in the additive group `G`.

The first message is the pair of component first messages; the response is
`(c₁, z₁, z₂)`, where `c₁` is the share of the first side and `c - c₁` that of the
second. The prover state is the share it sampled for the simulated side together
with the simulated response. -/
noncomputable def sigmaOR (sp₁ sp₂ : SigmaProtocol)
    (ι₁ : G ≃ sp₁.Challenge) (ι₂ : G ≃ sp₂.Challenge) : SigmaProtocolS where
  Statement := sp₁.Statement × sp₂.Statement
  Witness := sp₁.Witness ⊕ sp₂.Witness
  Message := sp₁.Message × sp₂.Message
  Challenge := G
  Response := G × sp₁.Response × sp₂.Response
  PState := G × Option (sp₁.Response ⊕ sp₂.Response)
  neState := inferInstanceAs (Nonempty (G × Option (sp₁.Response ⊕ sp₂.Response)))
  relation := fun x w =>
    match w with
    | .inl w₁ => sp₁.relation x.1 w₁
    | .inr w₂ => sp₂.relation x.2 w₂
  commit := fun x w =>
    match w with
    | .inl w₁ =>
      SPComp.bind (SPComp.sample G) fun c₂ =>
        SPComp.bind (sp₂.simulate x.2 (ι₂ c₂)) fun t₂ =>
          SPComp.bind (sp₁.commit x.1 w₁) fun a₁ =>
            SPComp.pure ((a₁, t₂.1), (c₂, some (.inr t₂.2)))
    | .inr w₂ =>
      SPComp.bind (SPComp.sample G) fun c₁ =>
        SPComp.bind (sp₁.simulate x.1 (ι₁ c₁)) fun t₁ =>
          SPComp.bind (sp₂.commit x.2 w₂) fun a₂ =>
            SPComp.pure ((t₁.1, a₂), (c₁, some (.inl t₁.2)))
  respond := fun x w s a c =>
    match w, s.2 with
    | .inl w₁, some (.inr z₂) =>
      SPComp.bind (sp₁.respond x.1 w₁ a.1 (ι₁ (c - s.1))) fun z₁ =>
        SPComp.pure (c - s.1, z₁, z₂)
    | .inr w₂, some (.inl z₁) =>
      SPComp.bind (sp₂.respond x.2 w₂ a.2 (ι₂ (c - s.1))) fun z₂ =>
        SPComp.pure (s.1, z₁, z₂)
    | _, _ => SPComp.fail
  verify := fun x a c z =>
    sp₁.verify x.1 a.1 (ι₁ z.1) z.2.1 && sp₂.verify x.2 a.2 (ι₂ (c - z.1)) z.2.2
  simulate := fun x c =>
    SPComp.bind (SPComp.sample G) fun c₁ =>
      SPComp.bind (sp₁.simulate x.1 (ι₁ c₁)) fun t₁ =>
        SPComp.bind (sp₂.simulate x.2 (ι₂ (c - c₁))) fun t₂ =>
          SPComp.pure ((t₁.1, t₂.1), (c₁, t₁.2, t₂.2))

/-- A witness for the left relation is a witness for the OR relation. -/
theorem sigmaOR_relation_left (sp₁ sp₂ : SigmaProtocol)
    (ι₁ : G ≃ sp₁.Challenge) (ι₂ : G ≃ sp₂.Challenge)
    (x₁ : sp₁.Statement) (x₂ : sp₂.Statement) (w₁ : sp₁.Witness)
    (hrel : sp₁.relation x₁ w₁) :
    (sigmaOR sp₁ sp₂ ι₁ ι₂).relation (x₁, x₂) (.inl w₁) := hrel

/-- A witness for the right relation is a witness for the OR relation. -/
theorem sigmaOR_relation_right (sp₁ sp₂ : SigmaProtocol)
    (ι₁ : G ≃ sp₁.Challenge) (ι₂ : G ≃ sp₂.Challenge)
    (x₁ : sp₁.Statement) (x₂ : sp₂.Statement) (w₂ : sp₂.Witness)
    (hrel : sp₂.relation x₂ w₂) :
    (sigmaOR sp₁ sp₂ ι₁ ι₂).relation (x₁, x₂) (.inr w₂) := hrel

/-- The honest run of Sigma-OR with a left witness: the right side is simulated at
a uniform share `c₂`, and the left side is the honest run of `Σ₁` at `c - c₂`. -/
theorem sigmaOR_realTranscriptGivenS_inl (sp₁ sp₂ : SigmaProtocol)
    (ι₁ : G ≃ sp₁.Challenge) (ι₂ : G ≃ sp₂.Challenge)
    (x : sp₁.Statement × sp₂.Statement) (w₁ : sp₁.Witness) (c : G) :
    realTranscriptGivenS (sigmaOR sp₁ sp₂ ι₁ ι₂) x (.inl w₁) c =
      SPComp.bind (SPComp.sample G) fun c₂ =>
        SPComp.bind (sp₂.simulate x.2 (ι₂ c₂)) fun t₂ =>
          SPComp.bind (realTranscriptGiven sp₁ x.1 w₁ (ι₁ (c - c₂))) fun t₁ =>
            SPComp.pure ((t₁.message, t₂.1), c, (c - c₂, t₁.response, t₂.2)) := by
  simp only [realTranscriptGivenS, realTranscriptGiven, sigmaOR, SPComp.monad_bind_eq,
    SPComp.monad_pure_eq, SPComp.bind_assoc, SPComp.pure_bind]

/-- The honest run of Sigma-OR with a right witness: the left side is simulated at
a uniform share `c₁`, and the right side is the honest run of `Σ₂` at `c - c₁`. -/
theorem sigmaOR_realTranscriptGivenS_inr (sp₁ sp₂ : SigmaProtocol)
    (ι₁ : G ≃ sp₁.Challenge) (ι₂ : G ≃ sp₂.Challenge)
    (x : sp₁.Statement × sp₂.Statement) (w₂ : sp₂.Witness) (c : G) :
    realTranscriptGivenS (sigmaOR sp₁ sp₂ ι₁ ι₂) x (.inr w₂) c =
      SPComp.bind (SPComp.sample G) fun c₁ =>
        SPComp.bind (sp₁.simulate x.1 (ι₁ c₁)) fun t₁ =>
          SPComp.bind (realTranscriptGiven sp₂ x.2 w₂ (ι₂ (c - c₁))) fun t₂ =>
            SPComp.pure ((t₁.1, t₂.message), c, (c₁, t₁.2, t₂.response)) := by
  simp only [realTranscriptGivenS, realTranscriptGiven, sigmaOR, SPComp.monad_bind_eq,
    SPComp.monad_pure_eq, SPComp.bind_assoc, SPComp.pure_bind]

/-- Completeness of Sigma-OR: from completeness of both components and simulators
whose transcripts verify. -/
theorem sigmaOR_completeness (sp₁ sp₂ : SigmaProtocol)
    (ι₁ : G ≃ sp₁.Challenge) (ι₂ : G ≃ sp₂.Challenge)
    (hc₁ : Completeness sp₁) (hc₂ : Completeness sp₂)
    (hs₁ : SimulatorAccepts sp₁) (hs₂ : SimulatorAccepts sp₂) :
    CompletenessS (sigmaOR sp₁ sp₂ ι₁ ι₂) := by
  intro x w (c : G) hrel
  cases w with
  | inl w₁ =>
    rw [sigmaOR_realTranscriptGivenS_inl sp₁ sp₂ ι₁ ι₂ x w₁ c]
    refine CatCrypt.Unary.pHoare_bind
      (CatCrypt.Unary.pHoare_sample (Q := fun _ _ => True) fun _ _ _ => trivial) fun c₂ => ?_
    refine CatCrypt.Unary.pHoare_bind (hs₂ x.2 (ι₂ c₂)) fun t₂ => ?_
    refine CatCrypt.Unary.pHoare_bind
      (Mid := fun t₁ _ => sp₁.verify x.1 t₁.message (ι₁ (c - c₂)) t₁.response = true ∧
        sp₂.verify x.2 t₂.1 (ι₂ c₂) t₂.2 = true) ?_ fun t₁ => ?_
    · intro h₀ hv₂ a h' hs
      exact ⟨hc₁ x.1 w₁ _ hrel h₀ trivial a h' hs, hv₂⟩
    · exact CatCrypt.Unary.pHoare_ret fun _ hv => by
        simp only [sigmaOR, sub_sub_cancel, Bool.and_eq_true]
        exact hv
  | inr w₂ =>
    rw [sigmaOR_realTranscriptGivenS_inr sp₁ sp₂ ι₁ ι₂ x w₂ c]
    refine CatCrypt.Unary.pHoare_bind
      (CatCrypt.Unary.pHoare_sample (Q := fun _ _ => True) fun _ _ _ => trivial) fun c₁ => ?_
    refine CatCrypt.Unary.pHoare_bind (hs₁ x.1 (ι₁ c₁)) fun t₁ => ?_
    refine CatCrypt.Unary.pHoare_bind
      (Mid := fun t₂ _ => sp₁.verify x.1 t₁.1 (ι₁ c₁) t₁.2 = true ∧
        sp₂.verify x.2 t₂.message (ι₂ (c - c₁)) t₂.response = true) ?_ fun t₂ => ?_
    · intro h₀ hv₁ a h' hs
      exact ⟨hv₁, hc₂ x.2 w₂ _ hrel h₀ trivial a h' hs⟩
    · exact CatCrypt.Unary.pHoare_ret fun _ hv => by
        simp only [sigmaOR, Bool.and_eq_true]
        exact hv

/-- Special soundness of Sigma-OR: two accepting transcripts with one first message
and different challenges have different shares on the first or on the second side,
and the extractor of that side gives a witness. -/
theorem sigmaOR_special_soundness [DecidableEq G] (sp₁ sp₂ : SigmaProtocol)
    (ι₁ : G ≃ sp₁.Challenge) (ι₂ : G ≃ sp₂.Challenge)
    (hSS₁ : SpecialSoundness sp₁) (hSS₂ : SpecialSoundness sp₂) :
    SpecialSoundness (sigmaOR sp₁ sp₂ ι₁ ι₂).toSigmaProtocol := by
  obtain ⟨ext₁, hext₁⟩ := hSS₁
  obtain ⟨ext₂, hext₂⟩ := hSS₂
  refine ⟨fun x tt => if h : tt.response1.1 = tt.response2.1 then
    .inr (ext₂ x.2 {
      message := tt.message.1.2
      challenge1 := ι₂ ((show G from tt.challenge1) - tt.response1.1)
      response1 := tt.response1.2.2
      challenge2 := ι₂ ((show G from tt.challenge2) - tt.response2.1)
      response2 := tt.response2.2.2
      accept1 := by
        have := tt.accept1
        simp only [sigmaOR, SigmaProtocolS.toSigmaProtocol, Bool.and_eq_true] at this
        exact this.2
      accept2 := by
        have := tt.accept2
        simp only [sigmaOR, SigmaProtocolS.toSigmaProtocol, Bool.and_eq_true] at this
        exact this.2
      diff := by
        intro heq
        apply tt.diff
        have hs := ι₂.injective heq
        rw [h] at hs
        exact (sub_left_inj (G := G)).mp hs })
    else
    .inl (ext₁ x.1 {
      message := tt.message.1.1
      challenge1 := ι₁ tt.response1.1
      response1 := tt.response1.2.1
      challenge2 := ι₁ tt.response2.1
      response2 := tt.response2.2.1
      accept1 := by
        have := tt.accept1
        simp only [sigmaOR, SigmaProtocolS.toSigmaProtocol, Bool.and_eq_true] at this
        exact this.1
      accept2 := by
        have := tt.accept2
        simp only [sigmaOR, SigmaProtocolS.toSigmaProtocol, Bool.and_eq_true] at this
        exact this.1
      diff := fun heq => h (ι₁.injective heq) }), fun x tt => ?_⟩
  have key : ∀ {p : Prop} [Decidable p] {α : Type} {R : α → Prop} {a : p → α}
      {b : ¬p → α}, (∀ h, R (a h)) → (∀ h, R (b h)) → R (dite p a b) := by
    intro p _ α R a b ha hb
    by_cases h : p
    · rw [dif_pos h]; exact ha h
    · rw [dif_neg h]; exact hb h
  exact key (fun _ => hext₂ _ _) (fun _ => hext₁ _ _)

/-- The simulated run of Sigma-OR: a uniform share `c₁`, the simulator of `Σ₁` at
`c₁`, and the simulated run of `Σ₂` at `c - c₁`. -/
theorem sigmaOR_simulatedTranscriptGivenS (sp₁ sp₂ : SigmaProtocol)
    (ι₁ : G ≃ sp₁.Challenge) (ι₂ : G ≃ sp₂.Challenge)
    (x : sp₁.Statement × sp₂.Statement) (c : G) :
    simulatedTranscriptGivenS (sigmaOR sp₁ sp₂ ι₁ ι₂) x c =
      SPComp.bind (SPComp.sample G) fun c₁ =>
        SPComp.bind (sp₁.simulate x.1 (ι₁ c₁)) fun t₁ =>
          SPComp.bind (simulatedTranscriptGiven sp₂ x.2 (ι₂ (c - c₁))) fun t₂ =>
            SPComp.pure ((t₁.1, t₂.message), c, (c₁, t₁.2, t₂.response)) := by
  simp only [simulatedTranscriptGivenS, simulatedTranscriptGiven, sigmaOR,
    SPComp.monad_bind_eq, SPComp.monad_pure_eq, SPComp.bind_assoc, SPComp.pure_bind]

/-- The simulated run of Sigma-OR with the two simulators exchanged, for a simulator
of `Σ₁` that does not use the heap. -/
theorem sigmaOR_simulatedTranscriptGivenS_swap (sp₁ sp₂ : SigmaProtocol)
    (ι₁ : G ≃ sp₁.Challenge) (ι₂ : G ≃ sp₂.Challenge)
    (hp₁ : ∀ x e, SPComp.IsPure (sp₁.simulate x e))
    (x : sp₁.Statement × sp₂.Statement) (c : G) :
    simulatedTranscriptGivenS (sigmaOR sp₁ sp₂ ι₁ ι₂) x c =
      SPComp.bind (SPComp.sample G) fun c₁ =>
        SPComp.bind (sp₂.simulate x.2 (ι₂ (c - c₁))) fun t₂ =>
          SPComp.bind (simulatedTranscriptGiven sp₁ x.1 (ι₁ c₁)) fun t₁ =>
            SPComp.pure ((t₁.message, t₂.1), c, (c₁, t₁.response, t₂.2)) := by
  simp only [simulatedTranscriptGivenS, simulatedTranscriptGiven, sigmaOR,
    SPComp.monad_bind_eq, SPComp.monad_pure_eq, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1
  funext c₁
  exact SPComp.isPure_bind_comm_left _ _ _ (hp₁ _ _)

/-- SHVZK of Sigma-OR: from SHVZK of both components and simulators that do not use
the heap. -/
theorem sigmaOR_shvzk_given (sp₁ sp₂ : SigmaProtocol)
    (ι₁ : G ≃ sp₁.Challenge) (ι₂ : G ≃ sp₂.Challenge)
    (hz₁ : SHVZK_given sp₁) (hz₂ : SHVZK_given sp₂)
    (hp₁ : ∀ x e, SPComp.IsPure (sp₁.simulate x e))
    (hp₂ : ∀ x e, SPComp.IsPure (sp₂.simulate x e)) :
    SHVZK_givenS (sigmaOR sp₁ sp₂ ι₁ ι₂) := by
  intro x w (c : G) hrel
  cases w with
  | inl w₁ =>
    rw [sigmaOR_realTranscriptGivenS_inl sp₁ sp₂ ι₁ ι₂ x w₁ c,
      sigmaOR_simulatedTranscriptGivenS_swap sp₁ sp₂ ι₁ ι₂ hp₁ x c]
    refine rHoare_bind (rHoare_sample_bij (Φ := fun _ _ => True) G G (Equiv.subLeft c))
      fun c₂ c₁ => ?_
    by_cases hc : c - c₂ = c₁
    · subst hc
      rw [sub_sub_cancel]
      refine rHoare_conseq (Φ := fun _ _ => True) (fun _ _ _ => trivial)
        (fun _ _ _ _ h => h) ?_
      refine rHoare_bind (rHoare_eq_self_of_isPure (hp₂ _ _)) fun t₂ t₂' => ?_
      intro h₁ h₂ (heq : t₂ = t₂')
      subst heq
      exact shvzk_given_map hz₁ hrel _
        (fun t₁ => ((t₁.message, t₂.1), c, (c - c₂, t₁.response, t₂.2))) h₁ h₂ trivial
    · intro _ _ hpre
      exact absurd (by simpa [Equiv.subLeft_apply] using hpre.2) hc
  | inr w₂ =>
    rw [sigmaOR_realTranscriptGivenS_inr sp₁ sp₂ ι₁ ι₂ x w₂ c,
      sigmaOR_simulatedTranscriptGivenS sp₁ sp₂ ι₁ ι₂ x c]
    refine rHoare_same_step fun c₁ => ?_
    refine rHoare_bind (rHoare_eq_self_of_isPure (hp₁ _ _)) fun t₁ t₁' => ?_
    intro h₁ h₂ (heq : t₁ = t₁')
    subst heq
    exact shvzk_given_map hz₂ hrel _
      (fun t₂ => ((t₁.1, t₂.message), c, (c₁, t₁.2, t₂.response))) h₁ h₂ trivial

end OR

/-! ## Instantiation: simpleSigma -/

/-- AND composition of simpleSigma with itself. -/
@[implicit_reducible]
noncomputable def simpleSigmaAND : SigmaProtocol :=
  sigmaAND simpleSigma simpleSigma rfl

/-- Completeness of the AND composition: for the prover-computed
    response, verification accepts. -/
theorem simpleSigmaAND_honest_complete (x₁ x₂ w₁ w₂ : Bool)
    (hr₁ : simpleSigma.relation x₁ w₁)
    (hr₂ : simpleSigma.relation x₂ w₂)
    (e : Bool) :
    let a₁ := w₁; let a₂ := w₂
    let z₁ := xor (xor a₁ w₁) e; let z₂ := xor (xor a₂ w₂) e
    simpleSigmaAND.verify (x₁, x₂) (a₁, a₂) e (z₁, z₂) = true := by
  simp_all [simpleSigmaAND, sigmaAND, simpleSigma]

end CatCrypt.Examples.SigmaCompositions
