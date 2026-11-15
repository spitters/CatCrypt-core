/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.ENNRealAverage
public import CatCryptCore.ForMathlib.GradeQuantale
public import CatCryptCore.ForMathlib.GaloisRing
public import CatCryptCore.ForMathlib.Matrix.Hermitian
public import CatCryptCore.ForMathlib.Matrix.ProjectorRewinding
public import CatCryptCore.ForMathlib.Matrix.SimultaneousDiag
public import CatCryptCore.ForMathlib.PMFSupport
public import CatCryptCore.ForMathlib.PMFPi
public import CatCryptCore.ForMathlib.PMFUniform
public import CatCryptCore.ForMathlib.PMFUniformDefs
public import CatCryptCore.ForMathlib.PMFOption
public import CatCryptCore.ForMathlib.PMFOuterMeasure
public import CatCryptCore.ForMathlib.ListLength
public import CatCryptCore.ForMathlib.UInt8Bytes
public import CatCryptCore.ForMathlib.EmbeddingFinSucc
public import CatCryptCore.ForMathlib.CategoryTheory.GrothendieckCocartesian
public import CatCryptCore.ForMathlib.CategoryTheory.KleisliOptionMonoidal
public import CatCryptCore.ForMathlib.CategoryTheory.Monoidal.IntConstruction
public import CatCryptCore.ForMathlib.CategoryTheory.Monoidal.IntConstructionMonoidal
public import CatCryptCore.ForMathlib.CategoryTheory.Monoidal.Traced
public import CatCryptCore.ForMathlib.CategoryTheory.ThinDoubleCategory
public import CatCryptCore.ForMathlib.Difunctional
public import CatCryptCore.ForMathlib.ENNRealNatCast
public import CatCryptCore.ForMathlib.GeometricMean
public import CatCryptCore.ForMathlib.LagrangeAtZero
public import CatCryptCore.ForMathlib.LawvereMetric
public import CatCryptCore.ForMathlib.LieTrotter
public import CatCryptCore.ForMathlib.LinearMapMatrix
public import CatCryptCore.ForMathlib.Matrix.ConeDuality
public import CatCryptCore.ForMathlib.Matrix.EffectOverlap
public import CatCryptCore.ForMathlib.Matrix.OverlapSum
public import CatCryptCore.ForMathlib.Matrix.PolarDecomposition
public import CatCryptCore.ForMathlib.Matrix.Schmidt
public import CatCryptCore.ForMathlib.Matrix.TraceDual
public import CatCryptCore.ForMathlib.Matrix.TraceInequalities
public import CatCryptCore.ForMathlib.Matrix.TraceNorm
public import CatCryptCore.ForMathlib.Matrix.KroneckerReindex
public import CatCryptCore.ForMathlib.Matrix.StarProjectionClosure
public import CatCryptCore.ForMathlib.Tactic.NoncommRingRel
public import CatCryptCore.ForMathlib.Tactic.PositivityStar
public import CatCryptCore.ForMathlib.Tactic.Spectral
public import CatCryptCore.ForMathlib.FejerKernel
public import CatCryptCore.ForMathlib.ShorReduction
public import CatCryptCore.ForMathlib.MatrixPolarization
public import CatCryptCore.ForMathlib.MatrixPosSemidef
public import CatCryptCore.ForMathlib.MultisetSum
public import CatCryptCore.ForMathlib.NatFindBounded
public import CatCryptCore.ForMathlib.Order.ScottInduction
public import CatCryptCore.ForMathlib.PFunctorChargeUnder
public import CatCryptCore.ForMathlib.PFunctorChargeVec
public import CatCryptCore.ForMathlib.PFunctorRestrict
public import CatCryptCore.ForMathlib.PMFMod
public import CatCryptCore.ForMathlib.Pocklington
public import CatCryptCore.ForMathlib.PrattCertificate
public import CatCryptCore.ForMathlib.Robertson
public import CatCryptCore.ForMathlib.SubmultiplicativeSummable
public import CatCryptCore.ForMathlib.TrotterBound
public import CatCryptCore.ForMathlib.ZModPow
public import CatCryptCore.ForMathlib.ZModValCard
public import CatCryptCore.ForMathlib.CategoryTheory.KleisliPMFMarkov
public import CatCryptCore.ForMathlib.Tactic.PositivityMatrix
public import CatCryptCore.ForMathlib.Tactic.TraceNf
public import CatCryptCore.ForMathlib.Tactic.TraceNfAttr

/-!
# Lemmas for Mathlib

Every declaration under `CatCryptCore/ForMathlib/` mentions only Mathlib
notions, carries a Mathlib-style name, and names in its module docstring the
Mathlib file it belongs in. The directory is the upstream queue: an entry
leaves it when the corresponding Mathlib pull request lands and the toolchain
pin includes it, at which point its uses name the Mathlib declaration.
A lemma belongs here only if Mathlib does not already have it; check with
`exact?`, Loogle and `lean_leansearch` before adding one, and record the
search in the docstring when a close neighbour exists.
-/
