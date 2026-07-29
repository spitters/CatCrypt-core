/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

-- Probability and core computation
import CatCryptCore.Prob.SDistr
import CatCryptCore.Prob.Coupling
import CatCryptCore.Prob.Support
import CatCryptCore.Prob.Conditional
import CatCryptCore.Prob.BirthdayBound
import CatCryptCore.Prob.SchwartzZippel
import CatCryptCore.Prob.XorBij
import CatCryptCore.Core.Basic
import CatCryptCore.Core.Location
import CatCryptCore.Core.Heap
import CatCryptCore.Core.Code
import CatCryptCore.Core.SPTree
import CatCryptCore.Core.StdDoBridge
import CatCryptCore.Core.GenHeap
import CatCryptCore.Core.GenHeapRandomOracle

-- Non-uniform sampling and the unbounded loop
import CatCryptCore.NonUniform

-- Relational logic (pRHL)
import CatCryptCore.Relational.Basic
import CatCryptCore.Relational.Judgment
import CatCryptCore.Relational.Rules
import CatCryptCore.Relational.Sync
import CatCryptCore.Relational.Frame
import CatCryptCore.Relational.Separation
import CatCryptCore.Relational.Reorder
import CatCryptCore.Relational.ForLoop

-- Package algebra
import CatCryptCore.Package.Interface
import CatCryptCore.Package.RawPackage
import CatCryptCore.Package.ValidPackage
import CatCryptCore.Package.Locations

-- Category-theoretic foundation
import CatCryptCore.Category.KlPMF
import CatCryptCore.Category.KlSPComp
import CatCryptCore.Category.Fam
import CatCryptCore.Category.PkgFam
import CatCryptCore.Category.Cocartesian
import CatCryptCore.Category.Affine
import CatCryptCore.Category.Effectus

-- Deep embedding
import CatCryptCore.Deep.RawCode
import CatCryptCore.Deep.Location
import CatCryptCore.Deep.Package
import CatCryptCore.Deep.Eval
import CatCryptCore.Deep.PackageEquiv
import CatCryptCore.Deep.PkgCategory
import CatCryptCore.Deep.Deterministic
import CatCryptCore.Deep.DeterministicInterp
import CatCryptCore.Deep.Strategy
import CatCryptCore.Deep.ProofFrog
import CatCryptCore.Deep.HybridDemo
import CatCryptCore.Deep.Bridge
import CatCryptCore.Deep.Tactics
import CatCryptCore.Deep.Reflect
import CatCryptCore.Deep.GamePackage
import CatCryptCore.Deep.OracleGamePackage
import CatCryptCore.Deep.ReflectUCHelpers

-- Semantic bridge
import CatCryptCore.Bridge.SemPkg
import CatCryptCore.Bridge.PkgEval
import CatCryptCore.Bridge.MonoidalBridge

-- Unary logic, nominal sets
import CatCryptCore.Unary
import CatCryptCore.Nominal

-- Tactics
import CatCryptCore.Tactics
import CatCryptCore.Tactics.BindVcgenSum
import CatCryptCore.Tactics.VC

-- Crypto foundation
import CatCryptCore.Crypto.Game
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Crypto.SDist
import CatCryptCore.Crypto.SDistrLift
import CatCryptCore.Crypto.UC
import CatCryptCore.Crypto.UCMonad
import CatCryptCore.Crypto.UCMonad.SPCompInstance
import CatCryptCore.Crypto.RC
import CatCryptCore.Crypto.UCAlg
import CatCryptCore.Crypto.UCComposition
import CatCryptCore.Crypto.UCDSL
import CatCryptCore.Crypto.AGM
import CatCryptCore.Crypto.SecurityDefs
import CatCryptCore.Crypto.Encryption
import CatCryptCore.Crypto.HybridArgument
import CatCryptCore.Crypto.NomAdvantage
import CatCryptCore.Crypto.EvalComplete
import CatCryptCore.Crypto.NomPkgBridge
import CatCryptCore.Crypto.EasyCryptBridge
import CatCryptCore.Crypto.BadEvent
import CatCryptCore.Crypto.ForkingLemma
import CatCryptCore.Crypto.GameReject
import CatCryptCore.Crypto.GeneralForkingLemma
import CatCryptCore.Crypto.SwitchingLemma
import CatCryptCore.Crypto.MultiQueryPRF
import CatCryptCore.Crypto.PRFAssumption
import CatCryptCore.Crypto.Assumptions.Catalog
import CatCryptCore.Crypto.BLSSig.Security

-- UC ideal functionalities (F_commit, F_ZK, F_OT) + shared group scaffolding
import CatCryptCore.Examples.GroupParam
import CatCryptCore.Crypto.Commitment.PedersenUC
import CatCryptCore.Crypto.ZK.SigmaUCZK
import CatCryptCore.Crypto.OT.DualModeOT

-- Classical curve mathematics
import CatCryptCore.Crypto.KeyAgreement.MontgomeryLadder
import CatCryptCore.Crypto.KeyAgreement.MontgomeryAsWeierstrass
import CatCryptCore.Crypto.KeyAgreement.MontgomeryXOnly
import CatCryptCore.Crypto.KeyAgreement.Curve25519
import CatCryptCore.Examples.DeepHybrid
import CatCryptCore.Examples.OneTimePad
import CatCryptCore.Examples.OT
import CatCryptCore.Examples.PRF
import CatCryptCore.Examples.PRFMAC
import CatCryptCore.Examples.PRFPRG
import CatCryptCore.Examples.PRG
import CatCryptCore.Examples.Sigma
import CatCryptCore.Examples.PKE.Scheme
import CatCryptCore.Examples.PKE.OneToMany
import CatCryptCore.Examples.PKE.MultiInstance
import CatCryptCore.Examples.Cryptobox.Scheme
import CatCryptCore.Examples.Cryptobox.KEY
import CatCryptCore.Examples.Cryptobox.PKEY
import CatCryptCore.Examples.Cryptobox.SAE
import CatCryptCore.Examples.Cryptobox.NIKE
import CatCryptCore.Examples.Cryptobox.PKAE
import CatCryptCore.Examples.Cryptobox.AE
import CatCryptCore.Examples.Cryptobox.Cryptobox
import CatCryptCore.Examples.Cryptobox.GameHopping
import CatCryptCore.Examples.Cryptobox.HYBRID
import CatCryptCore.Examples.Commitments.CommitmentScheme
import CatCryptCore.Examples.Commitments.PolyCommitScheme
import CatCryptCore.Examples.Commitments.KZG.Def
import CatCryptCore.Examples.Commitments.KZG.KnowledgeSoundness
import CatCryptCore.Examples.Commitments.Pedersen
import CatCryptCore.Examples.EncryptThenMAC
import CatCryptCore.Examples.BasicHash
import CatCryptCore.Examples.KEMDEM
import CatCryptCore.Examples.Schnorr
import CatCryptCore.Examples.SigmaProtocol
import CatCryptCore.Examples.ElGamal
import CatCryptCore.Examples.MAC
import CatCryptCore.Examples.SecretSharing
import CatCryptCore.Examples.ShamirSecretSharing
import CatCryptCore.Examples.Commitment
import CatCryptCore.Examples.CPAFromPRF
import CatCryptCore.Examples.EtMCCA
import CatCryptCore.Examples.CTRMode
import CatCryptCore.Examples.CBCMode
import CatCryptCore.Examples.DiffieHellman
import CatCryptCore.Examples.CyclicGroupDDH
import CatCryptCore.Examples.HashedElGamal
import CatCryptCore.Examples.ChaumPedersen
import CatCryptCore.Examples.UniversalHash
import CatCryptCore.Examples.DetCPA
import CatCryptCore.Examples.CoinToss
import CatCryptCore.Examples.INDCPA
import CatCryptCore.Examples.ElGamalDDH

/-! # CatCrypt Core — umbrella

Top-level entry point for the minimal-basis release. Re-exports the
program-logic + package-algebra stack, native forking lemmas, and the classical
Montgomery-curve and X25519 mathematics. VCVio / ArkLib interoperability is not
part of this basis — it lives in the separate `catcrypt-vcvio` / `catcrypt-arklib`
packages built on top of core. -/
