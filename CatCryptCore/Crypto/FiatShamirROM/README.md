# FiatShamirROM: Σ-protocols and the Fiat–Shamir transform

`CatCryptCore/Crypto/FiatShamirROM/` states Σ-protocols and the Fiat–Shamir transform in the
random-oracle model and proves their security with concrete bounds. Every bound holds for every
adversary through an explicit reduction defined in the file, with its running time. The
namespace is `CatCrypt.Crypto.FiatShamirROM`.

The constructions of the CFRG drafts
[draft-irtf-cfrg-sigma-protocols-03](https://datatracker.ietf.org/doc/draft-irtf-cfrg-sigma-protocols/)
and [draft-irtf-cfrg-fiat-shamir-03](https://datatracker.ietf.org/doc/draft-irtf-cfrg-fiat-shamir/)
are proved here; the comparison with the drafts and the extracted implementation of the crate
`sigma-proofs` are described in the
[SigmaProtocol README of the CatCrypt repository](https://github.com/spitters/CatCrypt/blob/master/CatCrypt/Crypto/SigmaProtocol/README.md).

## Modules

| Module | What it proves |
|---|---|
| [`Game.lean`](Game.lean) | The interface `Sigma` (statement, witness, commitment, challenge, response, extractor, simulator) with special soundness, perfect and statistical HVZK, completeness, unique responses and commitment min-entropy; the EUF-CMA game of Fiat–Shamir signatures |
| [`Reduction.lean`](Reduction.lean), [`SignerHybrid.lean`](SignerHybrid.lean), [`ProgFlag.lean`](ProgFlag.lean), [`StatHVZK.lean`](StatHVZK.lean) | EUF-CMA of Fiat–Shamir signatures by the forking lemma (`fiatShamir_rom_eufcma`), the signing-oracle simulation with statistical HVZK and aborts |
| [`StraightLine.lean`](StraightLine.lean), [`StraightLineCls.lean`](StraightLineCls.lean), [`StraightLineMk.lean`](StraightLineMk.lean) | EUF-CMA with straight-line extraction |
| [`KeyRecovery.lean`](KeyRecovery.lean), [`KeyRecoveryFlag.lean`](KeyRecoveryFlag.lean), [`KeyRecoveryMult.lean`](KeyRecoveryMult.lean) | Key-recovery reductions |
| [`Timed.lean`](Timed.lean) | Running-time theorems of the extraction reductions |
| [`Schnorr.lean`](Schnorr.lean) | Schnorr as a `Sigma`; its properties follow from the linear-relation protocol |
| [`MPCitH.lean`](MPCitH.lean) | Fiat–Shamir signatures of MPC-in-the-head proofs with all-but-one opening |
| [`Bridge.lean`](Bridge.lean) | A `Sigma` as a protocol of `CatCrypt.Examples.Sigma` |
| [`LinearRelation.lean`](LinearRelation.lean) | The Σ-protocol for a linear relation of draft-03 §3–4 (`linearSigma`): completeness, special soundness, perfect HVZK, unique responses for injective maps, equal acceptance of compact and batchable proofs, AND by concatenation; dlog, DLEQ, Pedersen, Okamoto and ElGamal instances |
| [`NIZK.lean`](NIZK.lean) | Fiat–Shamir with session identifier and statement in the hash: knowledge soundness against adaptive statements by forking (`ksExtractProb_ge`, with the extractor's running time) and zero knowledge with a programmable oracle (`zkReal_le_zkSim`) |
| [`DuplexSponge.lean`](DuplexSponge.lean) | The duplex sponge, session identifiers and codecs of the Fiat–Shamir draft: absorb and squeeze laws, prefix-free transcripts, decoding within 2^-128 of uniform, canonical parsing |
| [`DuplexSpongeNIZK.lean`](DuplexSpongeNIZK.lean), [`DuplexSpongeRawOracle.lean`](DuplexSpongeRawOracle.lean) | The duplex-sponge transform of a Σ-protocol reduced to `NIZK.lean`: knowledge soundness with the decoding bias added, against adversaries that read raw sponge bytes at arbitrary strings (`dsRawKsExtractProb_ge`, with the reduction's running time), and zero knowledge (`dsRawZkReal_le_zkSim`) |
