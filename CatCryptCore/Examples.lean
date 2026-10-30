/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Examples.GroupParam
public import CatCryptCore.Examples.DeepHybrid
public import CatCryptCore.Examples.OneTimePad
public import CatCryptCore.Examples.ReflectTacticDemo
public import CatCryptCore.Examples.OT
public import CatCryptCore.Examples.PRF
public import CatCryptCore.Examples.PRFTimed
public import CatCryptCore.Examples.PRFMAC
public import CatCryptCore.Examples.PRFMACTimed
public import CatCryptCore.Examples.PRFPRG
public import CatCryptCore.Examples.PRG
public import CatCryptCore.Examples.Sigma
public import CatCryptCore.Examples.PKE.Scheme
public import CatCryptCore.Examples.PKE.OneToMany
public import CatCryptCore.Examples.PKE.MultiInstance
public import CatCryptCore.Examples.Cryptobox.Scheme
public import CatCryptCore.Examples.Cryptobox.KEY
public import CatCryptCore.Examples.Cryptobox.PKEY
public import CatCryptCore.Examples.Cryptobox.PKEYQ
public import CatCryptCore.Examples.Cryptobox.SAE
public import CatCryptCore.Examples.Cryptobox.NIKE
public import CatCryptCore.Examples.Cryptobox.PKAE
public import CatCryptCore.Examples.Cryptobox.AE
public import CatCryptCore.Examples.Cryptobox.Cryptobox
public import CatCryptCore.Examples.Cryptobox.GameHopping
public import CatCryptCore.Examples.Cryptobox.HYBRID
public import CatCryptCore.Examples.Commitments.CommitmentScheme
public import CatCryptCore.Examples.Commitments.PolyCommitScheme
public import CatCryptCore.Examples.Commitments.KZG.Def
public import CatCryptCore.Examples.Commitments.KZG.KnowledgeSoundness
public import CatCryptCore.Examples.Commitments.Pedersen
public import CatCryptCore.Examples.EncryptThenMAC
public import CatCryptCore.Examples.BasicHash
public import CatCryptCore.Examples.KEMDEM
public import CatCryptCore.Examples.Schnorr
public import CatCryptCore.Examples.ElGamal
public import CatCryptCore.Examples.MAC
public import CatCryptCore.Examples.SecretSharing
public import CatCryptCore.Examples.ShamirSecretSharing
public import CatCryptCore.Examples.Commitment
public import CatCryptCore.Examples.CPAFromPRF
public import CatCryptCore.Examples.EtMCCA
public import CatCryptCore.Examples.CTRMode
public import CatCryptCore.Examples.CBCMode
public import CatCryptCore.Examples.DiffieHellman
public import CatCryptCore.Examples.CyclicGroupDDH
public import CatCryptCore.Examples.CyclicGroupModule
public import CatCryptCore.Examples.CyclicGroupRingPow
public import CatCryptCore.Examples.HashedElGamal
public import CatCryptCore.Examples.ChaumPedersen
public import CatCryptCore.Examples.UniversalHash
public import CatCryptCore.Examples.DetCPA
public import CatCryptCore.Examples.CoinToss
public import CatCryptCore.Examples.INDCPA
public import CatCryptCore.Examples.ElGamalDDH
public import CatCryptCore.Examples.ElGamalDDHKeyMsg
public import CatCryptCore.Examples.ElGamalUCConcrete
public import CatCryptCore.Examples.CBCModeTimed
public import CatCryptCore.Examples.CPAFromPRFTimed
public import CatCryptCore.Examples.DiffieHellmanTimed
public import CatCryptCore.Examples.ElGamalDDHTimed
public import CatCryptCore.Examples.ElGamalTimed
public import CatCryptCore.Examples.HashedElGamalTimed
public import CatCryptCore.Examples.KEMDEMTimed
public import CatCryptCore.Examples.OTTimed
public import CatCryptCore.Examples.PRGTimed

/-! # CatCrypt Core examples

Aggregator of the worked examples under `CatCryptCore.Examples`: game-based proofs of
textbook schemes (one-time pad, PRF/PRG constructions, ElGamal, KEM/DEM, cryptobox,
commitments, Sigma protocols) and their time-certified reductions. The umbrella
`CatCryptCore` does not import these modules; this module is a second root of the library,
so the default build and the documentation facet cover them.
-/
