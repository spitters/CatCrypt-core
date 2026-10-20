# SigmaProtocol: Σ-protocols, Fiat-Shamir and the CFRG drafts

`CatCryptCore/Crypto/SigmaProtocol/` holds the bridge from the hax extraction of the crate
`sigma-proofs-hax` to the Σ-protocol and Fiat-Shamir theorems of
[FiatShamirROM](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/README.md).

## Σ-protocols for linear relations and the CFRG drafts

The IRTF Crypto Forum Research Group specifies Σ-protocols and their Fiat-Shamir transform
in two drafts by Michele Orrù and Cathie Yun:
[draft-irtf-cfrg-sigma-protocols-03](https://datatracker.ietf.org/doc/draft-irtf-cfrg-sigma-protocols/)
("Sigma Proofs for Linear Relations") and
[draft-irtf-cfrg-fiat-shamir-03](https://datatracker.ietf.org/doc/draft-irtf-cfrg-fiat-shamir/)
(the duplex-sponge transform, after Chiesa and Orrù, TCC 2025). The Rust crate
[`sigma-proofs`](https://docs.rs/sigma-proofs) implements them on the duplex-sponge library
`spongefish`. CatCrypt states the drafts' constructions in Lean, proves their security with
concrete bounds, and connects the proofs to an extraction of the crate.

### What is proved

| Draft construction | What CatCrypt proves |
|---|---|
| The Σ-protocol for a linear relation (§3–4): commitment `map(nonces)`, response `nonce + challenge·witness`, verifier `map(z) = a + c·image` | Completeness ([`linearSigma_complete`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/LinearRelation.lean)), special soundness with an explicit extractor ([`linearSigma_specialSound`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/LinearRelation.lean)), perfect honest-verifier zero knowledge ([`linearSigma_perfectHVZK`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/LinearRelation.lean)) and unique responses for injective maps ([`linearSigma_uniqueResp`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/LinearRelation.lean)); Schnorr, DLEQ, Pedersen opening, Okamoto representation and ElGamal plaintext knowledge are instances |
| Batchable and compact proofs (§5) | The compact verifier accepts exactly the proofs the batchable verifier accepts ([`linearSigma_compactVerify_iff`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/LinearRelation.lean)) |
| AND composition (§3.4) | The concatenated relation holds iff both relations hold ([`holds_and_iff`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/LinearRelation.lean)), and the draft-03 validation of both relations gives that of the concatenation when the generator of the second relation occurs in one of its equations ([`validateInstance_and`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/LinearRelation.lean)) |
| OR composition (outside the draft) | Completeness, special soundness and HVZK of the Cramer–Damgård–Schoenmakers construction over any finite challenge group ([`sigmaOR_completeness`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Examples/SigmaCompositions.lean), [`sigmaOR_special_soundness`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Examples/SigmaCompositions.lean), [`sigmaOR_shvzk_given`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Examples/SigmaCompositions.lean)) |
| Fiat-Shamir with session identifier and statement in the hash (both drafts) | Knowledge soundness against an adversary choosing session, statement and proof adaptively, ε(ε/(q+1) − 1/\|Ch\|) ≤ extraction probability ([`ksExtractProb_ge`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/NIZK.lean)), with the extractor's running time ([`ksExtractor.timeBound_timed`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/NIZK.lean)); zero knowledge within qP·δ + qP·(qH+qP)·γ ([`zkReal_le_zkSim`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/NIZK.lean)) |
| Duplex sponge, session identifiers and codecs (Fiat-Shamir draft §3–6) | Absorb and squeeze laws ([`absorb_absorb`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/DuplexSponge.lean)); prefix-free transcripts ([`prefixFree_absorbedTranscript`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/DuplexSponge.lean)); `DecodeUint` within 2^-128 of uniform at Ns + 16 bytes ([`tvDist_decodeUintDist_le_two_pow`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/DuplexSponge.lean)); parsing accepts exactly the serializations and rejects trailing bytes ([`Codec.parseAll_eq_some_iff`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/DuplexSponge.lean)) |
| The duplex-sponge transform of a Σ-protocol | Knowledge soundness with the decoding bias (qH+1)·M/256^L added, against an adversary that queries the sponge at arbitrary byte strings ([`dsRawKsExtractProb_ge`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/DuplexSpongeRawOracle.lean)); zero knowledge with the oracle keyed by absorbed strings ([`dsRawZkReal_le_zkSim`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/DuplexSpongeRawOracle.lean)) |

Random-oracle Fiat-Shamir for signatures (EUF-CMA by the forking lemma, straight-line
extraction, aborts) and its quantum random-oracle variants are proved in the
[Fiat-Shamir modules of CatCrypt-core](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/README.md).

### The extracted implementation

The crate `sigma-proofs-hax` is a fork of `sigma-proofs` 0.4.1 rewritten in the subset of Rust
that hax extracts (nonces as inputs, index loops, functions returning updated values, group
operations through one trait), with the instance representation and validation of draft-03 §3;
its hax extraction is [`SigmaProofs_haxpipe`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/Extraction/SigmaProofs_haxpipe.lean).

- The extracted group operations are interpreted at ristretto255
  ([`defaultSigmaProofsDeps`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/SurfaceDeps.lean)), and the
  extracted prover, verifier, simulator and compact check are the components of `linearSigma`
  byte for byte ([`Instance_prover_response_eq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/SurfaceDeps.lean),
  [`Instance_verifier_ok_iff`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/SurfaceDeps.lean),
  [`extSigma_eq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/SurfaceDeps.lean)). Completeness, special
  soundness, zero knowledge and the Fiat-Shamir theorems above therefore hold for the extracted
  code ([`extSigma_ksExtractProb_ge`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/SurfaceDeps.lean),
  [`extSigma_dsKsExtractProb_ge`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/SurfaceDeps.lean)). The
  extracted validation accepts exactly the instances that satisfy the ten checks of draft-03
  §3.5, for equations with one image term and unit coefficients
  ([`validate_ok_iff`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/SurfaceDeps.lean), [`Instance_new_ok_iff`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/SurfaceDeps.lean)).
- The extracted batched verifier accepts exactly when a random linear combination of the
  verification equations holds; it accepts every proof the per-equation verifier accepts, and on a
  proof that verifier rejects it accepts with probability at most (m−1)/|scalars| over the
  combining scalar ([`batch_accept_prob_le`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/SigmaProofsBatchAnd.lean)). The extracted AND of two
  instances is `linearSigma` of the concatenated relation
  ([`extAndSigma_eq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/SigmaProofsBatchAnd.lean)), so it is complete, special sound and HVZK.
- A [differential test](https://github.com/spitters/CatCrypt/blob/master/sigma-proofs-hax/tests/differential.rs) compares the fork with the
  unmodified crate: identical encodings, commitments, responses, simulated transcripts and proof
  strings, and the same accept/reject result on correctly generated, tampered and truncated
  proofs and on proofs with appended bytes.
- The [test vectors of draft-03 Appendix A](https://github.com/spitters/CatCrypt/blob/master/sigma-proofs-hax/tests/draft_vectors.rs) (P-256
  and BLS12-381, both proof formats, valid and adversarial) run through the extracted core.
- Each linear combination is one call of the group trait's multi-scalar multiplication, `msm`
  (constant time in the scalars, for the prover) or `msm_vartime` (for public scalars: verifier,
  simulator, statement image); ristretto255 implements both by curve25519-dalek's Straus method.
  The extraction interprets both as the product of the bases raised to the scalars, and the
  theorems above are stated about the extracted code that makes these calls.
- Fixed-shape Schnorr and DLEQ functions over 64-bit limb arrays and status words
  ([`fixed.rs`](https://github.com/spitters/CatCrypt/blob/master/sigma-proofs-hax/src/fixed.rs)) are written in the domain of the CatCrypt
  compiler's front. Their Σ-protocols are `linearSigma` on the discrete-logarithm and DLEQ
  relations ([`fixedSchnorrSigma_eq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/FixedShape.lean),
  [`fixedDleqSigma_eq`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/FixedShape.lean)), so the security theorems above hold for
  them; on the instance the generic core builds for the same equations, the generic verifier and
  the fixed one agree ([`extSigma_verify_eq_fixedSchnorr`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SigmaProtocol/FixedShape.lean)).
- The statements that Signal's zkgroup and usernames prove with libsignal's `poksho` are linear
  relations over ristretto255
  ([`PokshoStatement.toRelation_holds_witness_iff`](https://github.com/spitters/CatCrypt/blob/master/CatCrypt/Crypto/Signal/Zkgroup/PokshoStatements.lean)), with
  the security theorems of `linearSigma`; a
  [test](https://github.com/spitters/CatCrypt/blob/master/sigma-proofs-hax/tests/poksho_statements.rs) runs the six statements through
  poksho and the fork on the same values.

The Rust code these theorems are about is the code that runs: the fork compiles with rustc,
with curve25519-dalek supplying the ristretto255 arithmetic behind the group trait, and produces
the same outputs as the reference crate. The extraction anchors the security proof (role 2 of
the
[hax-lean README](https://github.com/spitters/hax-lean/blob/master/README.md#three-roles-of-a-cryptographic-spec)),
and the crate's tests check it against the draft's vectors and the reference crate (role 3).

### Σ-protocols beyond the drafts

The drafts specify Σ-protocols for linear relations over prime-order groups with AND
composition. CatCrypt also proves:

- OR composition (Cramer–Damgård–Schoenmakers) over any finite challenge group, which the drafts
  leave out ([`sigmaOR_shvzk_given`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Examples/SigmaCompositions.lean)).
- Fiat–Shamir with aborts for lattice signatures: ML-DSA-65 as a Σ-protocol with statistical
  HVZK and a concrete random-oracle EUF-CMA bound
  ([`mldsa65_rom_eufcma_security_pow2`](https://github.com/spitters/CatCrypt/blob/master/CatCrypt/Crypto/MLDSA/Spec/CommitEntropy.lean)).
- MPC-in-the-head proofs with all-but-one opening and their Fiat–Shamir signatures
  ([`Params.eufcma_le`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/MPCitH.lean)), instantiated for MQOM
  ([`mqom_eufcma_reduction`](https://github.com/spitters/CatCrypt/blob/master/CatCrypt/Crypto/MQOM/Reduction.lean)), SDitH
  ([`sdith_eufcma_reduction`](https://github.com/spitters/CatCrypt/blob/master/CatCrypt/Crypto/SDitH/Reduction.lean)) and Picnic's ZKB++
  ([`eufcma_le`](https://github.com/spitters/CatCrypt/blob/master/CatCrypt/Crypto/Picnic/ZKBpp.lean)).
- Fiat–Shamir in the quantum random-oracle model for Σ-protocols with unique responses
  ([`fiatShamir_sigma_qrom`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QROM/FiatShamirSigma.lean)).

### What this adds to the drafts

- Machine-checked proofs of the drafts' constructions, with concrete bounds, where the drafts
  cite pen-and-paper results.
- A proof that the duplex-sponge transform reduces to Fiat-Shamir in the random-oracle model
  with the decoding bias as the only additive term, and machine-checked codec properties
  (prefix-freeness, decoding bias, canonical parsing).
- An implementation whose Σ core is proved to be the specified protocol and is checked against
  the draft's vectors and against the reference crate.
- Upstream `sigma-proofs` 0.4.1 implements an earlier instance representation than draft-03
  (identity at element index 0, three validation checks instead of ten); the fork follows the
  draft and the differential test records the inputs on which the two differ.

## UC zero knowledge for honest verifiers

- Real world ([`sigma_real`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/ZK/SigmaUCZK.lean)): on input (x, w) with R(x, w) the prover commits, the
  protocol draws a uniform challenge, the prover responds, and the adversary sees the transcript
  (a, e, z); on an input outside the relation the output is ⊥.
- Ideal functionality ([`sigma_ideal`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/ZK/SigmaUCZK.lean)): on input (x, w) with R(x, w) it reveals only the
  statement x; on an input outside the relation the output is ⊥.
- Simulator ([`sigma_uc_sim`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/ZK/SigmaUCZK.lean)): given x, it draws a challenge e, runs the special HVZK
  simulator of the Σ-protocol to obtain (a, z) without the witness, and hands (a, e, z) to the
  adversary.
- Theorem ([`sigma_uc_zk_secure`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/ZK/SigmaUCZK.lean)): special HVZK at every pair of the relation gives UC
  emulation of the ideal functionality at distance 0. The challenge is drawn by the protocol, so
  the verifier is honest and public-coin, and the theorem is the zero-knowledge direction;
  knowledge soundness of the non-interactive proof is [`ksExtractProb_ge`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/FiatShamirROM/NIZK.lean).

The Reduction, Security and FullSecurity files of this directory re-export these results.
