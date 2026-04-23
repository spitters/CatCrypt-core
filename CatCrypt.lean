/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-! # CatCrypt Core — umbrella

Top-level entry point for the minimal-basis release. Re-exports the
program-logic + package-algebra stack, native forking lemmas, Arklib-compatible
SNARK soundness, the VCVio interop bridge, the classical Montgomery-curve and
X25519 mathematics, and the verified RustCmd → Jasmin compilation pipeline. -/

-- Probability and core computation
import CatCrypt.Prob.SDistr
import CatCrypt.Prob.Coupling
import CatCrypt.Prob.Support
import CatCrypt.Prob.Conditional
import CatCrypt.Prob.BirthdayBound
import CatCrypt.Prob.SchwartzZippel
import CatCrypt.Prob.XorBij
import CatCrypt.Core.Basic
import CatCrypt.Core.Location
import CatCrypt.Core.Heap
import CatCrypt.Core.Code
import CatCrypt.Core.SPTree

-- Relational logic (pRHL)
import CatCrypt.Relational.Basic
import CatCrypt.Relational.Judgment
import CatCrypt.Relational.Rules
import CatCrypt.Relational.Sync
import CatCrypt.Relational.Frame
import CatCrypt.Relational.Reorder

-- Package algebra
import CatCrypt.Package.Interface
import CatCrypt.Package.RawPackage
import CatCrypt.Package.ValidPackage
import CatCrypt.Package.Locations

-- Category-theoretic foundation
import CatCrypt.Category.KlPMF
import CatCrypt.Category.KlSPComp
import CatCrypt.Category.Fam
import CatCrypt.Category.PkgFam
import CatCrypt.Category.Cocartesian
import CatCrypt.Category.Affine
import CatCrypt.Category.Effectus

-- Deep embedding
import CatCrypt.Deep.RawCode
import CatCrypt.Deep.Location
import CatCrypt.Deep.Package
import CatCrypt.Deep.Eval
import CatCrypt.Deep.PackageEquiv
import CatCrypt.Deep.PkgCategory
import CatCrypt.Deep.Deterministic
import CatCrypt.Deep.DeterministicInterp
import CatCrypt.Deep.Strategy
import CatCrypt.Deep.ProofFrog
import CatCrypt.Deep.HybridDemo
import CatCrypt.Deep.Bridge
import CatCrypt.Deep.Tactics

-- Semantic bridge
import CatCrypt.Bridge.SemPkg
import CatCrypt.Bridge.PkgEval
import CatCrypt.Bridge.MonoidalBridge

-- Unary logic, nominal sets
import CatCrypt.Unary
import CatCrypt.Nominal

-- Tactics
import CatCrypt.Tactics

-- Crypto foundation
import CatCrypt.Crypto.Game
import CatCrypt.Crypto.Advantage
import CatCrypt.Crypto.SDist
import CatCrypt.Crypto.SecurityDefs
import CatCrypt.Crypto.Encryption
import CatCrypt.Crypto.HybridArgument
import CatCrypt.Crypto.NomAdvantage
import CatCrypt.Crypto.ForkingLemma
import CatCrypt.Crypto.GeneralForkingLemma
import CatCrypt.Crypto.Assumptions.Catalog

-- Bridges: VCVio interop, Arklib soundness types
import CatCrypt.Crypto.Bridges.VCVioBridge
import CatCrypt.Crypto.Bridges.ArkLibTypes

-- Classical curve mathematics
import CatCrypt.Crypto.KeyAgreement.MontgomeryLadder
import CatCrypt.Crypto.KeyAgreement.MontgomeryAsWeierstrass
import CatCrypt.Crypto.KeyAgreement.MontgomeryXOnly
import CatCrypt.Crypto.KeyAgreement.Curve25519

-- Verified RustCmd → Jasmin compilation pipeline
import CatCrypt.Crypto.SecureCompilation.CryptoSSA
import CatCrypt.Crypto.Jasmin.RustCmd
import CatCrypt.Crypto.Jasmin.RustCmdBorrowCheck
import CatCrypt.Crypto.Jasmin.RustCmdToJasmin
import CatCrypt.Crypto.Jasmin.RustEmit
import CatCrypt.Crypto.Jasmin.JasminAST
import CatCrypt.Crypto.Jasmin.JasminTypes
import CatCrypt.Crypto.Jasmin.JasminVar
import CatCrypt.Crypto.Jasmin.JasminOps
import CatCrypt.Crypto.Jasmin.JasminSem
import CatCrypt.Crypto.Jasmin.JasminTranslate
import CatCrypt.Crypto.Jasmin.JasminToSSA
import CatCrypt.Crypto.Jasmin.PassFramework
import CatCrypt.Crypto.Jasmin.ISA
import CatCrypt.Crypto.Jasmin.ChaCha20QR
import CatCrypt.Crypto.Jasmin.Passes.ConstantFold
import CatCrypt.Crypto.Jasmin.Passes.NopElim
import CatCrypt.Crypto.Jasmin.Passes.DeadCode
