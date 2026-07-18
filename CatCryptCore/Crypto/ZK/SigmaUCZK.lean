/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.UC
import CatCryptCore.Crypto.SDist
import CatCryptCore.Examples.SigmaProtocol
import CatCryptCore.Tactics.BindVcgenSum

/-!
# Σ-Protocol to Honest-Verifier UC Zero-Knowledge via a Witness-Free Simulator

A Σ-protocol with special honest-verifier zero-knowledge (SHVZK) yields a
UC-secure **honest-verifier / public-coin** zero-knowledge proof at error `0`
(perfect ZK), with a **non-trivial** simulator that never uses the witness.

## Scope

The protocol itself samples the challenge, `e ← SPComp.sample sp.Challenge`
(see `sigma_real`), so the verifier is public-coin: it draws `e` uniformly and
independently of the commitment. The result is therefore honest-verifier UC-ZK.
SHVZK alone does not give malicious-verifier ZK, and this file does not claim it:
lifting to a verifier that chooses `e` adaptively as a function of the
commitment requires an additional mechanism — a challenge commitment (the
verifier commits to `e` before seeing `a`) or a Fiat–Shamir transform in the
random-oracle model.

`sigma_uc_zk_secure` covers the **ZK / simulation direction only** — it shows the
real prover's view is reproducible without the witness. It says nothing about
**knowledge soundness**: there is no extractor here, so this is not a full
realization of an `F_ZK` proof-of-knowledge functionality (which also requires
extracting a witness from a convincing prover, e.g. via special soundness and
rewinding).

## The transformation

Given a Σ-protocol `(commit, respond, simulate)`:

* the real prover knows the witness `w` and produces a transcript
  `(a, e, z)` via `commit`, a uniform (public-coin) challenge, then `respond`;
* the UC-ZK simulator does not know `w`: it samples a challenge `e` and runs
  `simulate x e` to produce `(a, z)` backwards.

SHVZK guarantees that the simulated transcript `(a, e, z)` is distributed exactly
as a real one, so the two views coincide even though the simulator never uses the
witness.

## Non-trivial simulator

`sigma_uc_sim` calls `simulate` in place of the real prover's `commit`/`respond`:

* real: `commit x w → (a, e, z)` — uses `w`;
* simulated: `simulate x e → (a, z)` — witness-free.

Producing valid-looking transcripts without the witness is exactly the
zero-knowledge property.

## Interface types

* `leak = Transcript` — the real world leaks the full transcript `(a, e, z)`.
* `sim_if = Statement` — the ideal hands the simulator only the statement `x`.

## References

* [Damgård, *On Σ-Protocols*]
-/

namespace CatCrypt.Crypto.ZK.SigmaUCZK

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Examples.SigmaProtocol
open scoped ENNReal

set_option autoImplicit false

variable (sp : SigmaProtocol)

/-! ## Transcript -/

/-- A Σ-protocol transcript: commitment, challenge, response. -/
structure Transcript where
  /-- The commitment (first message). -/
  commitment : sp.Message
  /-- The challenge. -/
  challenge : sp.Challenge
  /-- The response. -/
  response : sp.Response

/-! ## Real Protocol -/

/-- Real ZK prover: on input `(x, w)` with `R(x, w)`, runs the honest protocol and
    reveals the full transcript `(a, e, z)`. -/
noncomputable def sigma_real :
    sp.Statement × sp.Witness → SPComp (Unit ⊕ Transcript sp) :=
  fun ⟨x, w⟩ => do
    let a ← sp.commit x w
    let e ← SPComp.sample sp.Challenge
    let z ← sp.respond x w a e
    SPComp.pure (.inr ⟨a, e, z⟩)

/-! ## Ideal Functionality -/

/-- Ideal ZK: reveals only the statement, neither the witness nor the transcript.
    The simulator receives `x` and must produce a transcript without `w`. -/
noncomputable def sigma_ideal :
    sp.Statement × sp.Witness → SPComp (Unit ⊕ sp.Statement) :=
  fun ⟨x, _w⟩ => SPComp.pure (.inr x)

/-! ## Non-Trivial Simulator -/

/-- UC-ZK simulator: given only the statement `x`, sample a challenge `e`, run
    `simulate x e` to obtain `(a, z)`, and hand the transcript `(a, e, z)` to the
    adversary. Non-trivial because it calls `simulate` rather than the honest
    `commit`/`respond`; SHVZK guarantees the same distribution. -/
noncomputable def sigma_uc_sim
    (view : Type) (A : Transcript sp → SPComp view) :
    sp.Statement → SPComp view :=
  fun x => do
    let e ← SPComp.sample sp.Challenge
    let (a, z) ← sp.simulate x e
    A ⟨a, e, z⟩

/-! ## UC Specification -/

/-- UC spec for Σ-protocol UC-ZK: honest input is `(Statement × Witness)`, the real
    world leaks the full `Transcript`, and the ideal hands the simulator only the
    `Statement`. -/
noncomputable def sigmaUCZKSpec (V : Type) : UCSpec :=
  ⟨sp.Statement × sp.Witness, Unit, Transcript sp, sp.Statement, V⟩

/-! ## SHVZK Assumption -/

/-- Special honest-verifier zero-knowledge: for every statement `x`, witness `w`,
    and challenge `e`, the honestly generated `(a, z)` and the simulated `(a, z)`
    have the same distribution. This is what makes the witness-free simulator
    indistinguishable from the real prover. -/
def SHVZK : Prop :=
  ∀ (x : sp.Statement) (w : sp.Witness) (e : sp.Challenge),
    (do let a ← sp.commit x w
        let z ← sp.respond x w a e
        SPComp.pure (a, z)) =
    sp.simulate x e

/-! ## Nice-to-have (not formalized here)

Two natural extensions, each requiring machinery this file does not build:

* **Malicious-verifier ZK.** Replace the protocol's `SPComp.sample sp.Challenge`
  by a challenge chosen by an adversarial verifier `V*` (possibly depending on the
  commitment `a`), and restore honesty via a challenge commitment (the verifier
  commits to `e` before seeing `a`) or a Fiat–Shamir hash `e := H(x, a)` in the
  random-oracle model. The simulator then programs the random oracle instead of
  freely sampling `e`, and SHVZK is invoked at the programmed challenge.
* **Knowledge soundness / extractor.** Add a witness extractor from two accepting
  transcripts that share a commitment but have distinct challenges (special
  soundness) together with a rewinding argument, giving the soundness half of a
  full `F_ZK` proof-of-knowledge functionality. `sigma_uc_zk_secure` proves only
  the simulation direction.

Both are developed in the larger CatCrypt UC development built on top of this
basis (outside this minimal-basis release): a `ProofOfKnowledge` module supplies
the knowledge extractor via special soundness plus the forking/rewinding
argument (`sigma_is_pok`), and a Fiat–Shamir layer supplies the malicious-verifier
NIZK with a random-oracle-programming simulator. This file is the self-contained
honest-verifier simulation exemplar. -/

/-! ## Security Proof -/

/-- Under SHVZK the real and simulated views coincide pointwise. -/
theorem sigma_view_eq
    (hshvzk : SHVZK sp) (x : sp.Statement) (w : sp.Witness)
    (V : Type) (A : Transcript sp → SPComp V) :
    SPComp.bind (sigma_real sp (x, w)) (mapSum SPComp.pure A) =
    SPComp.bind (sigma_ideal sp (x, w))
      (mapSum SPComp.pure (sigma_uc_sim sp V A)) := by
  unfold sigma_real sigma_ideal sigma_uc_sim
  bind_vcgen_sum
  -- Commute the (pure) challenge sample past `commit` so both sides lead with
  -- `bind (sample Challenge) (fun e => …)`. This higher-order rewrite must be
  -- supplied explicitly since the continuation cannot be inferred.
  rw [← SPComp.isPure_bind_comm_left (SPComp.sample sp.Challenge) (sp.commit x w)
    (fun e a => SPComp.bind (sp.respond x w a e) (fun z =>
      SPComp.bind (A ⟨a, e, z⟩) (fun v => SPComp.pure (Sum.inr v))))
    (SPComp.sample_isPure _)]
  bind_vcgen_sum
  rename_i e
  have hshvzk_e := hshvzk x w e
  have key : ∀ (K : sp.Message → sp.Response → SPComp (Unit ⊕ V)),
      SPComp.bind (sp.commit x w) (fun a =>
        SPComp.bind (sp.respond x w a e) (fun z => K a z)) =
      SPComp.bind (sp.simulate x e) (fun p => K p.1 p.2) := by
    intro K
    have := congr_arg (fun c => SPComp.bind c (fun p => K p.1 p.2)) hshvzk_e
    simp only [ssprove_simpl] at this
    exact this
  exact key _

/-- **A Σ-protocol with SHVZK gives honest-verifier UC zero-knowledge at `ε = 0`**
    (perfect ZK), with a witness-free simulator. The protocol is public-coin: it
    samples the challenge `e ← SPComp.sample sp.Challenge` in `sigma_real`, so this
    is honest-verifier UC-ZK, not malicious-verifier UC-ZK (SHVZK alone does not
    give the latter — that needs a challenge commitment or a ROM Fiat–Shamir
    transform). The theorem covers the ZK / simulation direction only:
    `sigma_uc_sim` reproduces the prover's view via `simulate`, without the
    witness; it does not establish knowledge soundness (there is no extractor).
    (genuine UC) -/
theorem sigma_uc_zk_secure
    (hshvzk : SHVZK sp) (V : Type) :
    UCEmulates 0 (sigmaUCZKSpec sp V) (sigma_real sp) (sigma_ideal sp) := by
  intro A
  use sigma_uc_sim sp V A
  show sdist _ _ ≤ 0
  have h : ∀ a, (sigma_real sp a).bind (mapSum SPComp.pure A) =
           (sigma_ideal sp a).bind (mapSum SPComp.pure (sigma_uc_sim sp V A)) :=
    fun ⟨x, w⟩ => sigma_view_eq sp hshvzk x w V A
  refine le_of_eq ?_
  calc sdist (fun a => (sigma_real sp a).bind (mapSum SPComp.pure A))
             (fun a => (sigma_ideal sp a).bind (mapSum SPComp.pure (sigma_uc_sim sp V A)))
      = sdist (fun a => (sigma_ideal sp a).bind (mapSum SPComp.pure (sigma_uc_sim sp V A)))
              (fun a => (sigma_ideal sp a).bind (mapSum SPComp.pure (sigma_uc_sim sp V A))) := by
          congr 1; funext a; exact h a
    _ = 0 := sdist_self _

end CatCrypt.Crypto.ZK.SigmaUCZK
