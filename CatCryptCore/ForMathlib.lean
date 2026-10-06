/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.GradeQuantale
public import CatCryptCore.ForMathlib.Matrix.Hermitian

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
