/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.CryptoWord
public import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Tactics.DeriveReduction

/-!
# Tests of `time_bound` on values bound before a costed bind

The costed form that `derive_reduction` produces for a reduction with a value bound by `let`
before a costed bind `y` names `y` twice: once in a step cost `y.1`, with the value inlined,
and once in the tree `y.2.bind k`, under a `have` binder. `time_bound` bounds such forms alone,
in three shapes: `delay (C + y.1) (y.2.bind k)` (`miniPrefix`), the same form in the branch of
a sample node (`miniSample`), and two nested key generations (`miniNested`).

## Main results

* `miniPrefix_time`, `miniSample_time`, `miniNested_time`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.AutoTimePrefixTest

open CatCrypt.Core CatCrypt.Crypto

/-- A hash and a key generation, as the dependency structures of the protocols provide them. -/
structure Kit (W : Type) where
  /-- A data function. -/
  sha256 : W → W
  /-- A key generation. -/
  keygen : SPComp (W × W)

variable {W : Type} [CryptoWord W] (deps : Kit W)

/-- A value bound by `let` before a key generation, then the distinguisher. -/
noncomputable def miniPrefix (A : W → SPComp Bool) (z : W) : SPComp Bool :=
  (do
    let u := deps.sha256 z
    let ⟨i, _⟩ ← deps.keygen
    pure (CryptoWord.wxor u i)).bind A

/-- A uniform sample, a value bound by `let` and a key generation, then the distinguisher. -/
noncomputable def miniSample (A : W → SPComp Bool) (z : W) : SPComp Bool :=
  (do
    let s ← SPComp.sample W
    let u := deps.sha256 (CryptoWord.wxor s z)
    let ⟨i, _⟩ ← deps.keygen
    pure (CryptoWord.wxor u i)).bind A

/-- Two key generations, each after a value bound by `let`, then the distinguisher. -/
noncomputable def miniNested (A : W → SPComp Bool) (z : W) : SPComp Bool :=
  (do
    let u := deps.sha256 z
    let ⟨i, _⟩ ← deps.keygen
    let v := deps.sha256 (CryptoWord.wxor u i)
    let ⟨j, _⟩ ← deps.keygen
    pure (CryptoWord.wxor v j)).bind A

derive_reduction miniPrefix (adv := A)

derive_reduction miniSample (adv := A)

derive_reduction miniNested (adv := A)

variable (A : W → SPTree.Timed Bool) (ACost : W → ℕ) (sha256 : W → W) (sha256Cost : W → ℕ)
  (keygen : SPTree.Timed (W × W)) {T a t : ℕ}

/-- The form `delay (C + y.1) (y.2.bind k)`, `y` under a `have` binder in the tree. -/
theorem miniPrefix_time (z : W) (hA : ∀ o, (A o).time ≤ T) (hAc : ∀ o, ACost o ≤ a)
    (hsha : ∀ x, sha256Cost x ≤ t) :
    SPTree.Timed.stepTime (miniPrefix.tree.timed deps A ACost z sha256 sha256Cost keygen) ≤
      keygen.time + (T + a + t + 10) := by
  time_bound

/-- The form `sample γ f n (fun b => c b + y.1) (fun b => y.2)` followed by a bind. -/
theorem miniSample_time (z : W) (hA : ∀ o, (A o).time ≤ T) (hAc : ∀ o, ACost o ≤ a)
    (hsha : ∀ x, sha256Cost x ≤ t) :
    SPTree.Timed.stepTime (miniSample.tree.timed deps A ACost z sha256 sha256Cost keygen) ≤
      keygen.time + (T + a + t + 10) := by
  time_bound

/-- Two nested prefixes of the form of `miniPrefix_time`. -/
theorem miniNested_time (z : W) (hA : ∀ o, (A o).time ≤ T) (hAc : ∀ o, ACost o ≤ a)
    (hsha : ∀ x, sha256Cost x ≤ t) :
    SPTree.Timed.stepTime (miniNested.tree.timed deps A ACost z sha256 sha256Cost keygen) ≤
      keygen.time + (keygen.time + (T + a + 2 * t + 10)) := by
  time_bound

end CatCrypt.Tactics.AutoTimePrefixTest
