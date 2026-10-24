/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Tests of `derive_reduction` on two reduction shapes

* `r2Red`: a reduction over an adversary structure whose parameter is a scheme built by a
  reducible definition from a structure binder, with a data field of that binder used both in
  the scheme and in the body (the shape of `cs_ddh_reduction`);
* `r3Red`: a computation binder `d` that the types of other binders mention, run once and
  passed as data to a parameter function (the shape of `redEnc`).

Each is derived by `derive_reduction` and has a time theorem by `derive_time_bound`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveReductionRefusalsTest

open CatCrypt.Core

/-! ## An adversary over a scheme built from a structure binder -/

/-- A hash function. -/
structure R2Hash where
  hash : ℕ → ℕ

/-- A scheme with a ciphertext type and a decryption computation. -/
structure R2Scheme where
  Ct : Type
  dec : Ct → SPComp ℕ

/-- Decryption through the hash. -/
def r2dec (H : R2Hash) (c : ℕ) : ℕ := H.hash c + 1

/-- The scheme of the hash `H`. -/
@[reducible] noncomputable def r2toScheme (H : R2Hash) : R2Scheme where
  Ct := ℕ
  dec := fun c => SPComp.pure (r2dec H c)

/-- A two-phase adversary against the scheme `E`, with a state type. -/
structure R2Adv (E : R2Scheme) where
  State : Type
  phase1 : (E.Ct → SPComp ℕ) → SPComp (ℕ × State)
  phase2 : E.Ct → State → SPComp Bool

/-- Phase one with the decryption oracle, phase two on a hashed challenge. -/
noncomputable def r2Red (H : R2Hash) (adv : R2Adv (r2toScheme H)) (x : ℕ) : SPComp Bool := do
  let (m, st) ← adv.phase1 (r2toScheme H).dec
  adv.phase2 (H.hash (m + x)) st

derive_reduction r2Red

derive_time_bound r2Red.tree

/-! ## A computation binder passed as data -/

/-- A parameter computed from a distribution and a number. -/
def r3par (_d : SPComp ℕ) (n : ℕ) : ℕ := n + 1

/-- Run `d` and call the adversary, whose type depends on `d`, on the residue of the result. -/
noncomputable def r3Red (d : SPComp ℕ) (_hs : SPComp.IsPure d)
    (A : Fin (r3par d 2) → SPComp Bool) : SPComp Bool := do
  let v ← d
  A ⟨v % 3, Nat.mod_lt _ (by decide)⟩

derive_reduction r3Red

derive_time_bound r3Red.tree

end CatCrypt.Tactics.DeriveReductionRefusalsTest
