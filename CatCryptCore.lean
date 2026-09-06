/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

-- Probability and core computation
public import CatCryptCore.Prob.SDistr
public import CatCryptCore.Prob.Coupling
public import CatCryptCore.Prob.Support
public import CatCryptCore.Prob.Conditional
public import CatCryptCore.Prob.BirthdayBound
public import CatCryptCore.Prob.SchwartzZippel
public import CatCryptCore.Prob.XorBij
public import CatCryptCore.Core.Basic
public import CatCryptCore.Core.Location
public import CatCryptCore.Core.Heap
public import CatCryptCore.Core.Code
public import CatCryptCore.Core.SPTree
public import CatCryptCore.Core.StdDoBridge
public import CatCryptCore.Core.GenHeap
public import CatCryptCore.Core.GenHeapRandomOracle

-- Non-uniform sampling and the unbounded loop
public import CatCryptCore.NonUniform

-- Relational logic (pRHL)
public import CatCryptCore.Relational.Basic
public import CatCryptCore.Relational.Judgment
public import CatCryptCore.Relational.Rules
public import CatCryptCore.Relational.Sync
public import CatCryptCore.Relational.Frame
public import CatCryptCore.Relational.Separation
public import CatCryptCore.Relational.Reorder
public import CatCryptCore.Relational.ForLoop

-- Package algebra
public import CatCryptCore.Package.Interface
public import CatCryptCore.Package.RawPackage
public import CatCryptCore.Package.ValidPackage
public import CatCryptCore.Package.Locations

-- Category-theoretic foundation
public import CatCryptCore.Category.KlPMF
public import CatCryptCore.Category.KlSPComp
public import CatCryptCore.Category.Fam
public import CatCryptCore.Category.PkgFam
public import CatCryptCore.Category.Cocartesian
public import CatCryptCore.Category.Affine
public import CatCryptCore.Category.Effectus

-- Deep embedding
public import CatCryptCore.Deep.RawCode
public import CatCryptCore.Deep.Location
public import CatCryptCore.Deep.Package
public import CatCryptCore.Deep.Eval
public import CatCryptCore.Deep.PackageEquiv
public import CatCryptCore.Deep.PkgCategory
public import CatCryptCore.Deep.Deterministic
public import CatCryptCore.Deep.DeterministicInterp
public import CatCryptCore.Deep.Strategy
public import CatCryptCore.Deep.ProofFrog
public import CatCryptCore.Deep.HybridDemo
public import CatCryptCore.Deep.Bridge
public import CatCryptCore.Deep.Tactics
public import CatCryptCore.Deep.Reflect
public import CatCryptCore.Deep.GamePackage
public import CatCryptCore.Deep.OracleGamePackage
public import CatCryptCore.Deep.ReflectUCHelpers

-- Semantic bridge
public import CatCryptCore.Bridge.SemPkg
public import CatCryptCore.Bridge.PkgEval
public import CatCryptCore.Bridge.MonoidalBridge

-- Unary logic, nominal sets
public import CatCryptCore.Unary
public import CatCryptCore.Nominal

-- Tactics
public import CatCryptCore.Tactics
public import CatCryptCore.Tactics.BindVcgenSum
public import CatCryptCore.Tactics.VC

-- Crypto foundation
public import CatCryptCore.Crypto.Game
public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Crypto.SDist
public import CatCryptCore.Crypto.SDistrLift
public import CatCryptCore.Crypto.UC
public import CatCryptCore.Crypto.UCMonad
public import CatCryptCore.Crypto.UCMonad.SPCompInstance
public import CatCryptCore.Crypto.RC
public import CatCryptCore.Crypto.UCAlg
public import CatCryptCore.Crypto.UCComposition
public import CatCryptCore.Crypto.UCDSL
public import CatCryptCore.Crypto.AGM
public import CatCryptCore.Crypto.SecurityDefs
public import CatCryptCore.Crypto.Encryption
public import CatCryptCore.Crypto.HybridArgument
public import CatCryptCore.Crypto.NomAdvantage
public import CatCryptCore.Crypto.EvalComplete
public import CatCryptCore.Crypto.NomPkgBridge
public import CatCryptCore.Crypto.EasyCryptBridge
public import CatCryptCore.Crypto.BadEvent
public import CatCryptCore.Crypto.ForkingLemma
public import CatCryptCore.Crypto.GameReject
public import CatCryptCore.Crypto.GeneralForkingLemma
public import CatCryptCore.Crypto.SwitchingLemma
public import CatCryptCore.Crypto.MultiQueryPRF
public import CatCryptCore.Crypto.PRFAssumption
public import CatCryptCore.Crypto.Assumptions.Catalog
public import CatCryptCore.Crypto.BLSSig.Security

-- UC ideal functionalities (F_commit, F_ZK, F_OT) + shared group scaffolding
public import CatCryptCore.Examples.GroupParam
public import CatCryptCore.Crypto.Commitment.PedersenUC
public import CatCryptCore.Crypto.ZK.SigmaUCZK
public import CatCryptCore.Crypto.OT.DualModeOT

-- Classical curve mathematics
public import CatCryptCore.Crypto.KeyAgreement.MontgomeryLadder
public import CatCryptCore.Crypto.KeyAgreement.MontgomeryAsWeierstrass
public import CatCryptCore.Crypto.KeyAgreement.MontgomeryXOnly
public import CatCryptCore.Crypto.KeyAgreement.Curve25519
public import CatCryptCore.Examples.DeepHybrid
public import CatCryptCore.Examples.OneTimePad
public import CatCryptCore.Examples.OT
public import CatCryptCore.Examples.PRF
public import CatCryptCore.Examples.PRFMAC
public import CatCryptCore.Examples.PRFPRG
public import CatCryptCore.Examples.PRG
public import CatCryptCore.Examples.Sigma
public import CatCryptCore.Examples.PKE.Scheme
public import CatCryptCore.Examples.PKE.OneToMany
public import CatCryptCore.Examples.PKE.MultiInstance
public import CatCryptCore.Examples.Cryptobox.Scheme
public import CatCryptCore.Examples.Cryptobox.KEY
public import CatCryptCore.Examples.Cryptobox.PKEY
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
public import CatCryptCore.Examples.SigmaProtocol
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
public import CatCryptCore.Examples.HashedElGamal
public import CatCryptCore.Examples.ChaumPedersen
public import CatCryptCore.Examples.UniversalHash
public import CatCryptCore.Examples.DetCPA
public import CatCryptCore.Examples.CoinToss
public import CatCryptCore.Examples.INDCPA
public import CatCryptCore.Examples.ElGamalDDH

/-! # CatCrypt Core — umbrella

Top-level entry point for the minimal-basis release. Re-exports the
program-logic + package-algebra stack, native forking lemmas, and the classical
Montgomery-curve and X25519 mathematics. VCVio / ArkLib interoperability is not
part of this basis — it lives in the separate `catcrypt-vcvio` / `catcrypt-arklib`
packages built on top of core. -/

@[expose] public section
