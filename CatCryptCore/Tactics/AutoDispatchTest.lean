/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoDispatch
public meta import CatCryptCore.Tactics.AutoDispatch

/-!
# Tests for `catcrypt_auto`

One example per shape of `CatCryptCore.Tactics.AutoDispatch`, a goal whose
shape is detected but whose arms fail, and goals on which an arm exceeds its
heartbeat budget.
-/

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Relational CatCrypt.Crypto CatCrypt.Unary
open scoped ENNReal

namespace CatCrypt.Tactics.AutoDispatchTest

/-! ## One goal per shape -/

/-- Side condition in `do` form (the shape of `ik_real` in NoiseIK/Spec.lean). -/
example : SPComp.IsPure (do
    let a ← SPComp.sample Bool
    let b ← SPComp.sample Bool
    pure (a && b) : SPComp Bool) := by
  catcrypt_auto

/-- `NoFail` side condition in `>>=` form. -/
example {α β : Type} (a : α) (f : α → SPComp β) (hf : ∀ x, SPComp.NoFail (f x)) :
    SPComp.NoFail ((pure a : SPComp α) >>= f) := by
  catcrypt_auto

/-- A pure prefix followed by identical code on both sides. -/
example {α β : Type} (a : α) (c : α → SPComp β) :
    rHoare eqPre (SPComp.bind (SPComp.pure a) c) (c a) eqPost := by
  catcrypt_auto

/-- Two hop leaves of a triangle chain (the shape of KEMTLS/Reduction.lean:161). -/
example {α : Type} (G₀ G₁ G₂ : SPComp α) (A : α → SPComp Bool) (ε₁ ε₂ : ℝ≥0∞)
    (h₁ : AdvantageA G₀ G₁ A ≤ ε₁) (h₂ : AdvantageA G₁ G₂ A ≤ ε₂) :
    AdvantageA G₀ G₁ A + AdvantageA G₁ G₂ A ≤ ε₁ + ε₂ := by
  catcrypt_auto

/-- Read after a write to another location (Examples/Cryptobox/PKEY.lean:439). -/
example (h₁ : Heap) (l l' : Location) (v : l.ty) (b : l'.ty) (hid : l.id ≠ l'.id)
    (hset : Heap.get h₁ l' = b) :
    Heap.get (h₁.set l v) l' = b := by
  catcrypt_auto

/-- Monad-law normalisation of an `SPComp` chain. -/
example {α β : Type} (a : α) (c : SPComp β) (f : α → SPComp β) (hf : f a = c) :
    SPComp.bind (SPComp.bind (SPComp.pure a) f) SPComp.pure = c := by
  catcrypt_auto

/-- A goal of no registered shape. -/
example (n : ℕ) (h : n = 3) : n + 1 = 4 := by
  catcrypt_auto

/-! ## Failure within the budget -/

/-- The shape is detected and every arm fails on a false bound. -/
example (G₀ G₁ : SPComp Bool) : True := by
  fail_if_success have _ : Advantage G₀ G₁ ≤ 0 := by catcrypt_auto
  trivial

/-- `simp_all` rewrites `f n` to `f (n + 1)` without end and reaches the
recursion limit; the runtime exception is caught and `grind` closes the goal. -/
example (f : ℕ → ℕ) (_h : ∀ n, f n = f (n + 1)) (h₇ : f 0 = 7) : f 0 = 7 := by
  catcrypt_auto

-- Under a budget of one heartbeat unit the `aesop` arm exceeds it; the
-- heartbeat exception is caught and reported as the failure of the arm.
set_option catcrypt_auto.maxHeartbeats 1 in
example : True := by
  fail_if_success
    have _ : SPComp.NoFail ((pure true : SPComp Bool) >>= fun b => pure (!b)) := by catcrypt_auto
  trivial

/-! ## Suggestion -/

/-- `catcrypt_auto?` suggests the closing arm with its normalisation. -/
example {α β : Type} (a : α) (f : α → SPComp β) (hf : ∀ x, SPComp.NoFail (f x)) :
    SPComp.NoFail ((pure a : SPComp α) >>= f) := by
  catcrypt_auto?

end CatCrypt.Tactics.AutoDispatchTest
