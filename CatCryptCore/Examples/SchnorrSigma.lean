/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCryptCore.Package
public import CatCryptCore.Invariant
public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Relational.Rules
public import CatCryptCore.Examples.Sigma
public import CatCryptCore.Tactics.Basic
public import CatCryptCore.Tactics.Sync
public import CatCryptCore.Crypto.Assumptions.DLGroupParam
public import CatCryptCore.Crypto.FiatShamirROM.Schnorr

/-!
# Schnorr identification and signatures over `GroupParam`

The Schnorr Σ-protocol for knowledge of a discrete logarithm over an abstract
prime-order group `CatCrypt.Examples.GroupParam`, as a `SigmaProtocol` of the
`CatCrypt.Examples.Sigma` framework, and the Schnorr signature scheme obtained
from it by the Fiat-Shamir transform.

The module `CatCryptCore.Examples.Schnorr` (re-exported as
`CatCrypt.Examples.Schnorr`) states the protocol over the group `G₁` of a
`PairingGroup` with scalars `ZMod p`: its acceptance relation, special soundness
as a statement about two transcripts, and the discrete-logarithm solver obtained
from a forking Schnorr forger. This module states the protocol over
`GroupParam` with an explicit commit/respond/simulate interface, proves
SHVZK by a coupling, and states special soundness as the `SpecialSoundness`
property of the Σ-protocol. Both modules use the namespace
`CatCrypt.Examples.Schnorr`; the verifier and the special-soundness theorems of
this module carry the suffix `GP` / `_gp`.

## Main results

* `schnorrSigma` — Schnorr identification as a `SigmaProtocol`, with verifier
  `schnorrVerifyGP`.
* `schnorr_SHVZK_visible`, `schnorr_SHVZK` — special honest-verifier zero
  knowledge for the visible part of the transcript, by the bijection
  `r ↦ r + e·w`.
* `schnorr_special_soundness_gp` — special soundness of `schnorrSigma gp`.
* `schnorrVerifySig_eq_fs`, `schnorrSign_eq_fs` — signing and verification are
  the Fiat-Shamir transform of `FiatShamirROM.schnorrSigma`.

## Overview

The Schnorr protocol is a Sigma protocol for proving knowledge of a discrete
logarithm. Given a cyclic group G with generator g of prime order q:
- **Statement**: public key h = g^w
- **Witness**: secret key w (discrete log of h)
- **Protocol**:
  1. Prover samples r, sends commitment a = g^r
  2. Verifier sends random challenge e
  3. Prover sends response z = r + e*w (mod q)
  4. Verifier checks g^z = a * h^e

## Fiat-Shamir Transform

The Fiat-Shamir transform converts the identification protocol into a signature
scheme by replacing the verifier's random challenge with a hash of the commitment
and message: e = H(a, m).

- **Sign(sk=w, m)**: Sample r, compute a = g^r, e = H(a, m), z = r + e*w; return (a, z)
- **Verify(pk=h, m, (a, z))**: Compute e = H(a, m); check g^z = a * h^e

## Security

This file proves SHVZK and special soundness of the identification protocol.
`schnorrVerifySig_eq_fs` and `schnorrSign_eq_fs` identify signing and
verification with the Fiat–Shamir transform of the core Σ-protocol
`FiatShamirROM.schnorrSigma`, whose EUF-CMA bound in the random-oracle model
by the forking reduction to the discrete logarithm is
`FiatShamirROM.schnorr_fs_rom_eufcma`.

## References

* [Schnorr, Efficient Identification and Signatures for Smart Cards]
* [Damgard, On Sigma Protocols]
* Rocq SSProve: `theories/Crypt/examples/Schnorr.v`
-/

@[expose] public section

namespace CatCrypt.Examples.Schnorr

open CatCrypt.Core
open CatCrypt.Package
open CatCrypt.Prob
open CatCrypt.Relational
open CatCrypt.Invariant
open CatCrypt.Crypto
open CatCrypt.Examples.Sigma

/-! ## Abstract Group Parameters

The group parameters are `CatCrypt.Examples.GroupParam` from CatCrypt-core, a cyclic
group of prime order with its scalar field. The export keeps the name
`Schnorr.GroupParam` resolving to it. -/

export CatCrypt.Examples (GroupParam)

/-! The scalar-field lemmas `scalarMul_neg` and `scalarNeg_mul` are those of
`CatCrypt.Examples.GroupParam`. -/

export CatCrypt.Examples (scalarMul_neg scalarNeg_mul)

/-! ## Schnorr Protocol Types

Following the Rocq `MyParam` module. -/

variable (gp : GroupParam)

/-- Schnorr witness: the secret key w such that h = g^w -/
abbrev Witness := gp.Scalar

/-- Schnorr statement: the public key h -/
abbrev Statement := gp.G

/-- Schnorr commitment message: (r, a = g^r) where r is the internal randomness
    and a is the externally visible commitment.
    Note: For SHVZK, we need r to be available to the respond function, hence
    we include it in the message type. In a real implementation, r would be
    stored in private state. -/
abbrev Message := gp.Scalar × gp.G

/-- Schnorr challenge: random scalar e -/
abbrev Challenge := gp.Scalar

/-- Schnorr response: z = r + e*w -/
abbrev Response := gp.Scalar

/-- The discrete log relation: R(h, w) iff h = g^w -/
def dlRelation (h : Statement gp) (w : Witness gp) : Prop :=
  h = gp.exp w

/-! ## Schnorr as Sigma Protocol

The Schnorr protocol algorithms following Rocq's `MyAlg` module. -/

/-- Schnorr protocol commitment: sample random r, return (r, a = g^r)
    The random r is included for the response phase to compute z = r + e*w. -/
noncomputable def schnorrCommit (_h : Statement gp) (_w : Witness gp) : SPComp (Message gp) := do
  let r ← SPComp.sample gp.Scalar
  SPComp.pure (r, gp.exp r)

/-- Schnorr protocol response: compute z = r + e*w
    The randomness r comes from the message (r, a). -/
noncomputable def schnorrRespond (_h : Statement gp) (w : Witness gp)
    (ra : Message gp) (e : Challenge gp) : SPComp (Response gp) :=
  -- r is the first component of the message
  SPComp.pure (gp.scalarAdd ra.1 (gp.scalarMul e w))

/-- Schnorr verification: check g^z = a * h^e

    This is the core verification equation of the Schnorr protocol.
    When the prover follows the protocol with relation h = g^w:
    - a = g^r (commitment, second component of message)
    - z = r + e*w (response)
    - g^z = g^(r + e*w) = g^r * g^(e*w) = a * (g^w)^e = a * h^e
    Note: verification uses only the visible part (a = g^r), not r. -/
def schnorrVerifyGP (h : Statement gp) (ra : Message gp)
    (e : Challenge gp) (z : Response gp) : Bool :=
  gp.exp z == gp.groupMul ra.2 (gp.groupExp h e)

/-- Schnorr simulator: given challenge e, produce transcript without witness
    Sample z uniformly, compute a = g^z * h^(-e)
    The simulated message includes a "fake" r computed as z - e*w (mod q),
    but since we don't know w, we just use z as a placeholder for r.
    The verifier only sees a = g^z * h^(-e), which is consistent. -/
noncomputable def schnorrSimulate (h : Statement gp) (e : Challenge gp) :
    SPComp (Message gp × Response gp) := do
  let z ← SPComp.sample gp.Scalar
  -- a = g^z * h^(-e) = g^z * (g^w)^(-e) = g^(z - w*e)
  -- When z = r + e*w, we get a = g^r as expected
  -- For simulation, we compute a from z and e
  let a := gp.groupMul (gp.exp z) (gp.groupInv (gp.groupExp h e))
  -- The "r" component is set to z for internal consistency (not used in verification)
  -- In fact, when h = g^w, the correct r would be z - e*w
  SPComp.pure ((z, a), z)

/-- Schnorr extractor: from two accepting transcripts, extract witness
    Given (ra, e, z) and (ra, e', z') with e ≠ e':
    z - z' = (r + e*w) - (r + e'*w) = (e - e')*w
    So w = (z - z') / (e - e')
    Note: The message ra = (r, a) must be the same for both transcripts. -/
def schnorrExtractor (_h : Statement gp) (_ra : Message gp)
    (e : Challenge gp) (e' : Challenge gp)
    (z : Response gp) (z' : Response gp) : Option (Witness gp) :=
  -- w = (z - z') / (e - e')
  -- Requires e ≠ e' (different challenges)
  if e == e' then none
  else some (gp.scalarDiv (gp.scalarSub z z') (gp.scalarSub e e'))

/-! ## Schnorr Sigma Protocol Instance -/

/-- Schnorr identification as a Sigma protocol.

    The message type is (Scalar × G) = (r, g^r) to allow the respond function
    to compute z = r + e*w deterministically. The verifier only uses the
    second component (g^r) for verification. -/
@[implicit_reducible]
noncomputable def schnorrSigma : SigmaProtocol where
  Statement := gp.G
  Witness := gp.Scalar
  Message := gp.Scalar × gp.G
  Challenge := gp.Scalar
  Response := gp.Scalar
  finChallenge := gp.finScalar
  neChallenge := gp.neScalar
  relation := dlRelation gp
  commit := schnorrCommit gp
  respond := schnorrRespond gp
  verify := schnorrVerifyGP gp
  simulate := schnorrSimulate gp

/-! ## Fiat-Shamir Transform: Schnorr Signatures

The Fiat-Shamir transform converts the interactive identification protocol
into a non-interactive signature scheme by using a hash function to
generate the challenge from the commitment and message. -/

/-- Hash function type for Fiat-Shamir: maps (commitment, message) to challenge -/
abbrev HashFunction (gp : GroupParam) (MsgType : Type) := gp.G → MsgType → gp.Scalar

/-- Schnorr signature scheme parameters -/
structure SchnorrSigParams (gp : GroupParam) where
  /-- Message type -/
  MsgType : Type
  /-- Message type is finite (for uniform sampling in security games) -/
  [finMsg : Fintype MsgType]
  [neMsg : Nonempty MsgType]
  /-- Hash function for Fiat-Shamir -/
  hash : HashFunction gp MsgType

attribute [instance] SchnorrSigParams.finMsg SchnorrSigParams.neMsg

/-- Schnorr signature: (commitment a, response z) -/
structure SchnorrSignature (gp : GroupParam) where
  commitment : gp.G
  response : gp.Scalar

/-- Schnorr key pair -/
structure SchnorrKeyPair (gp : GroupParam) where
  secretKey : gp.Scalar  -- w
  publicKey : gp.G       -- h = g^w

/-- Generate a Schnorr key pair -/
noncomputable def schnorrKeyGen : SPComp (SchnorrKeyPair gp) := do
  let sk ← SPComp.sample gp.Scalar
  let pk := gp.exp sk
  SPComp.pure ⟨sk, pk⟩

/-- Sign a message using Schnorr signature scheme

    Sign(sk=w, m):
    1. Sample random r
    2. Compute commitment a = g^r
    3. Compute challenge e = H(a, m)
    4. Compute response z = r + e*w
    5. Return signature (a, z) -/
@[implicit_reducible]
noncomputable def schnorrSign (params : SchnorrSigParams gp)
    (kp : SchnorrKeyPair gp) (m : params.MsgType) : SPComp (SchnorrSignature gp) := do
  let r ← SPComp.sample gp.Scalar
  let a := gp.exp r
  let e := params.hash a m
  let z := gp.scalarAdd r (gp.scalarMul e kp.secretKey)
  SPComp.pure ⟨a, z⟩

/-- Verify a Schnorr signature

    Verify(pk=h, m, (a, z)):
    1. Compute challenge e = H(a, m)
    2. Check g^z = a * h^e
    Note: The signature only contains (a, z), not the internal r.
    We pass a dummy r value since schnorrVerifyGP only uses the second component. -/
@[implicit_reducible]
def schnorrVerifySig (params : SchnorrSigParams gp)
    (pk : gp.G) (m : params.MsgType) (sig : SchnorrSignature gp) : Bool :=
  let e := params.hash sig.commitment m
  -- schnorrVerifyGP expects (r, a) but only uses a (second component)
  schnorrVerifyGP gp pk (gp.scalarZero, sig.commitment) e sig.response

/-! ## The Fiat–Shamir Σ-protocol of the scheme

Signing and verification are the Fiat–Shamir transform of the Σ-protocol
`FiatShamirROM.schnorrSigma gp` of CatCrypt-core. Its EUF-CMA bound in the
random-oracle model, by the explicit forking reduction to the discrete
logarithm, is `FiatShamirROM.schnorr_fs_rom_eufcma`. -/

/-- Verification of a signature `(a, z)` on `m` runs the verifier of
    `FiatShamirROM.schnorrSigma gp` on the transcript `(a, H(a, m), z)`. -/
theorem schnorrVerifySig_eq_fs (params : SchnorrSigParams gp) (pk : gp.G)
    (m : params.MsgType) (sig : SchnorrSignature gp) :
    schnorrVerifySig gp params pk m sig =
      (CatCrypt.Crypto.FiatShamirROM.schnorrSigma gp).verify pk sig.commitment
        (params.hash sig.commitment m) sig.response := rfl

/-- Signing samples the prover randomness `r` and returns the commitment and the
    response of `FiatShamirROM.schnorrSigma gp` at the challenge `H(g^r, m)`. -/
theorem schnorrSign_eq_fs (params : SchnorrSigParams gp) (kp : SchnorrKeyPair gp)
    (m : params.MsgType) :
    schnorrSign gp params kp m = SPComp.bind (SPComp.sample gp.Scalar) fun r =>
      let P := CatCrypt.Crypto.FiatShamirROM.schnorrSigma gp
      SPComp.pure ⟨P.commit kp.publicKey kp.secretKey r,
        P.respond kp.publicKey kp.secretKey r
          (params.hash (P.commit kp.publicKey kp.secretKey r) m)⟩ := rfl

/-! ## Security Theorems -/

/-- Visible transcript equality for Schnorr: compares only the externally visible
    parts of the transcript (the commitment g^r, challenge, and response).
    The internal randomness r in the message is not compared. -/
def visibleTranscriptEq (t₁ t₂ : Transcript (schnorrSigma gp)) : Prop :=
  t₁.message.2 = t₂.message.2 ∧ t₁.challenge = t₂.challenge ∧
    t₁.response = t₂.response

/-- SHVZK for Schnorr protocol (visible parts): the simulator produces transcripts
    whose visible parts are indistinguishable from real protocol executions.

    This follows from the bijection between:
    - Real: sample r, output ((r, g^r), e, r + e*w)
    - Simulated: sample z, output ((z, g^z * h^(-e)), e, z)

    The bijection f(r) = r + e*w maps real randomness to simulated response.

    **Proof:**
    When the relation h = g^w holds:
    - Real visible transcript: (g^r, e, r + e*w)
    - Simulated visible transcript: (g^z * h^(-e), e, z)

    The mapping r -> z = r + e*w is a bijection on the scalar field.
    Under this bijection:
    - Commitment: g^z * h^(-e) = g^(r+ew) * (g^w)^(-e) = g^(r+ew-ew) = g^r
    - Challenge: e = e
    - Response: z = r + e*w

    So the visible parts are identically distributed. -/
theorem schnorr_SHVZK_visible : ∀ x w e, (schnorrSigma gp).relation x w →
    rHoare
      (fun _ _ => True)
      (realTranscriptGiven (schnorrSigma gp) x w e)
      (simulatedTranscriptGiven (schnorrSigma gp) x e)
      (fun t₁ _ t₂ _ => visibleTranscriptEq gp t₁ t₂) := by
  intro x w e hrel
  unfold realTranscriptGiven simulatedTranscriptGiven
  simp only [schnorrSigma, schnorrCommit, schnorrRespond, schnorrSimulate]
  ssprove_code_simpl
  apply rHoare_bij_step (gp.addEquiv (gp.scalarMul e w)); intro r
  apply rHoare_ret; intro _ _ _
  simp only [schnorrSigma, dlRelation] at hrel
  subst hrel
  exact ⟨(gp.sim_commit_eq w r e).symm, rfl, rfl⟩

/-- SHVZK for Schnorr protocol with internal challenge sampling.

    This theorem proves that when the challenge is sampled uniformly at random
    (rather than provided as input), the real and simulated transcripts have
    indistinguishable visible parts.

    **Key insight:** Since `schnorr_SHVZK_visible` holds for ALL challenges `e`,
    we can use it after uniformly sampling `e`:
    1. Swap the sampling order on the real side (sample e before r)
    2. Both sides now sample `e` first (diagonal coupling)
    3. For each fixed `e`, the bijection `r ↦ z = r + e*w` couples the remaining samples

    **Why internal sampling matters:**
    - In `realTranscript`, challenge is sampled AFTER commit
    - In `simulatedTranscript`, challenge is sampled BEFORE simulate
    - We use `SDistr.bind_comm` to swap the order on the real side
    - This aligns both sides to sample `e` first

    **Note:** This proves visible transcript equality, which is the cryptographically
    relevant property. Full transcript equality (`t₁ = t₂`) cannot be proven due to
    internal randomness in the Message type - see docstring above `schnorr_SHVZK_visible`. -/
theorem schnorr_SHVZK : ∀ x w, (schnorrSigma gp).relation x w →
    rHoare
      (fun _ _ => True)
      (realTranscript (schnorrSigma gp) x w)
      (simulatedTranscript (schnorrSigma gp) x)
      (fun t₁ _ t₂ _ => visibleTranscriptEq gp t₁ t₂) := by
  intro x w hrel
  unfold realTranscript simulatedTranscript
  simp only [schnorrSigma, schnorrCommit, schnorrRespond, schnorrSimulate]
  ssprove_code_simpl
  ssprove_swap_samples_lhs 1
  apply rHoare_same_step; intro e
  apply rHoare_bij_step (gp.addEquiv (gp.scalarMul e w)); intro r
  apply rHoare_ret; intro _ _ _
  simp only [schnorrSigma, dlRelation] at hrel
  subst hrel
  exact ⟨(gp.sim_commit_eq w r e).symm, rfl, rfl⟩

/-- Special soundness for Schnorr: from two accepting transcripts with
    different challenges, extract the witness.

    Given:
    - (a, e, z) accepting: g^z = a * h^e
    - (a, e', z') accepting: g^z' = a * h^(e')
    - e != e'

    Dividing: g^(z-z') = h^(e-e')
    So: h = g^((z-z')/(e-e'))
    Witness: w = (z-z')/(e-e') -/
theorem schnorr_special_soundness_gp : SpecialSoundness (schnorrSigma gp) := by
  use fun x tt => schnorrExtractor gp x tt.message tt.challenge1 tt.challenge2
                    tt.response1 tt.response2 |>.getD gp.scalarZero
  intro x tt
  have hacc1 := tt.accept1
  have hacc2 := tt.accept2
  simp only [schnorrSigma, schnorrVerifyGP, beq_eq_decide, decide_eq_true_eq] at hacc1 hacc2
  simp only [schnorrSigma, dlRelation, schnorrExtractor, beq_eq_decide, decide_eq_true_eq,
    tt.diff, ↓reduceIte, Option.getD_some]
  exact (gp.exp_extract_eq x _ _ _ _ _ hacc1 hacc2 tt.diff).symm

/-! The discrete-logarithm game and advantage are those of CatCrypt-core
(`GroupParam.dlGame`, `GroupParam.DL_Advantage`), exported under this namespace. -/
export CatCrypt.Examples.GroupParam (dlGame DL_Advantage)

end CatCrypt.Examples.Schnorr
