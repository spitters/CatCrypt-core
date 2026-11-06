/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHPassiveHops
public import CatCryptCore.Crypto.AKE.X3DHPassiveKeygen
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Costed forms of the X3DH hop reductions

`derive_reduction` reflects the DDH reductions `ddhRed1` … `ddhRed4` and the KDF reduction
`kdfReduction` of `X3DHPassiveHops`, and the DDH reductions `ddhRedK2`, `ddhRedK3`, `ddhRedK4`
of `X3DHPassiveKeygen`, whose earlier replaced values are drawn by key generation, into
computation trees and derives their costed forms `R.tree.timed`, with the compilation theorems
`R.compile_tree` and the erasure theorems `R.tree.erase_timed`. The primitives of a reduction (the key generation, the ECDH function,
the KDF and the adversary's `run`) are parameters of its costed tree with their cost
companions.

## Main results

With key generation of time at most `Tk`, the adversary's `run` of time at most `T` and call
cost at most `a`, the KDF of cost at most `c` and the ECDH function of cost at most `e`:

* `ddhRed1.tree.timeBound_timed` — time at most `3 * Tk + T + a + c + 3 * e + 5`;
* `ddhRed2.tree.timeBound_timed` — time at most `3 * Tk + T + a + c + 2 * e + 5`;
* `ddhRed3.tree.timeBound_timed` — time at most `3 * Tk + T + a + c + e + 5`;
* `ddhRed4.tree.timeBound_timed` — time at most `3 * Tk + T + a + c + 5`;
* `kdfReduction.tree.timeBound_timed` — time at most `5 * Tk + T + a + 1`;
* `ddhRedK2.tree.timeBound_timed` — time at most `4 * Tk + T + a + c + 2 * e + 4`;
* `ddhRedK3.tree.timeBound_timed` — time at most `5 * Tk + T + a + c + e + 4`;
* `ddhRedK4.tree.timeBound_timed` — time at most `6 * Tk + T + a + c + 4`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.Session.X3DHHops

open CatCrypt.Core CatCrypt.Crypto.Signal.X3DH

derive_reduction ddhRed1

derive_reduction ddhRed2

derive_reduction ddhRed3

derive_reduction ddhRed4

derive_reduction kdfReduction

derive_reduction ddhRedK2

derive_reduction ddhRedK3

derive_reduction ddhRedK4

variable {W : Type} [SampleableType W]
/-- **Time of the hop-1 reduction**: three key generations of time at most `Tk`, three ECDH
calls of cost at most `e`, the KDF of cost at most `c` and the adversary of time `T` and call
cost `a`. -/
theorem ddhRed1.tree.timeBound_timed (P : X3DHParams W)
    (A : KI_Adversary P) (g_a g_b z : W)
    (kdf : W → W → W → W → W) (kdfCost : W → W → W → W → ℕ)
    (ecdh : W → W → W) (ecdhCost : W → W → ℕ) (keygen : SPTree.Timed (W × W))
    (run : W → X3DHTranscript W → SPTree.Timed Bool) (runCost : W → X3DHTranscript W → ℕ)
    {Tk T a c e : ℕ} (hk : keygen.time ≤ Tk) (hA : ∀ x y, (run x y).time ≤ T)
    (hAc : ∀ x y, runCost x y ≤ a) (hc : ∀ w₁ w₂ w₃ w₄, kdfCost w₁ w₂ w₃ w₄ ≤ c)
    (he : ∀ w₁ w₂, ecdhCost w₁ w₂ ≤ e) :
    SPTree.Timed.stepTime (ddhRed1.tree.timed P A g_a g_b z kdf kdfCost ecdh ecdhCost keygen
      run runCost) ≤ 3 * Tk + T + a + c + 3 * e + 5 := by
  time_bound
/-- **Time of the hop-2 reduction**: three key generations, one uniform sample, two ECDH
calls, the KDF and the adversary. -/
theorem ddhRed2.tree.timeBound_timed (P : X3DHParams W)
    (A : KI_Adversary P) (g_a g_b z : W)
    (kdf : W → W → W → W → W) (kdfCost : W → W → W → W → ℕ)
    (ecdh : W → W → W) (ecdhCost : W → W → ℕ) (keygen : SPTree.Timed (W × W))
    (run : W → X3DHTranscript W → SPTree.Timed Bool) (runCost : W → X3DHTranscript W → ℕ)
    {Tk T a c e : ℕ} (hk : keygen.time ≤ Tk) (hA : ∀ x y, (run x y).time ≤ T)
    (hAc : ∀ x y, runCost x y ≤ a) (hc : ∀ w₁ w₂ w₃ w₄, kdfCost w₁ w₂ w₃ w₄ ≤ c)
    (he : ∀ w₁ w₂, ecdhCost w₁ w₂ ≤ e) :
    SPTree.Timed.stepTime (ddhRed2.tree.timed P A g_a g_b z kdf kdfCost ecdh ecdhCost keygen
      run runCost) ≤ 3 * Tk + T + a + c + 2 * e + 5 := by
  time_bound
/-- **Time of the hop-3 reduction**: three key generations, two uniform samples, one ECDH
call, the KDF and the adversary. -/
theorem ddhRed3.tree.timeBound_timed (P : X3DHParams W)
    (A : KI_Adversary P) (g_a g_b z : W)
    (kdf : W → W → W → W → W) (kdfCost : W → W → W → W → ℕ)
    (ecdh : W → W → W) (ecdhCost : W → W → ℕ) (keygen : SPTree.Timed (W × W))
    (run : W → X3DHTranscript W → SPTree.Timed Bool) (runCost : W → X3DHTranscript W → ℕ)
    {Tk T a c e : ℕ} (hk : keygen.time ≤ Tk) (hA : ∀ x y, (run x y).time ≤ T)
    (hAc : ∀ x y, runCost x y ≤ a) (hc : ∀ w₁ w₂ w₃ w₄, kdfCost w₁ w₂ w₃ w₄ ≤ c)
    (he : ∀ w₁ w₂, ecdhCost w₁ w₂ ≤ e) :
    SPTree.Timed.stepTime (ddhRed3.tree.timed P A g_a g_b z kdf kdfCost ecdh ecdhCost keygen
      run runCost) ≤ 3 * Tk + T + a + c + e + 5 := by
  time_bound
/-- **Time of the hop-4 reduction**: three key generations, three uniform samples, the KDF
and the adversary. -/
theorem ddhRed4.tree.timeBound_timed (P : X3DHParams W)
    (A : KI_Adversary P) (g_a g_b z : W)
    (kdf : W → W → W → W → W) (kdfCost : W → W → W → W → ℕ) (keygen : SPTree.Timed (W × W))
    (run : W → X3DHTranscript W → SPTree.Timed Bool) (runCost : W → X3DHTranscript W → ℕ)
    {Tk T a c : ℕ} (hk : keygen.time ≤ Tk) (hA : ∀ x y, (run x y).time ≤ T)
    (hAc : ∀ x y, runCost x y ≤ a) (hc : ∀ w₁ w₂ w₃ w₄, kdfCost w₁ w₂ w₃ w₄ ≤ c) :
    SPTree.Timed.stepTime (ddhRed4.tree.timed P A g_a g_b z kdf kdfCost keygen run runCost) ≤
      3 * Tk + T + a + c + 5 := by
  time_bound
/-- **Time of the KDF reduction**: five key generations and the adversary. -/
theorem kdfReduction.tree.timeBound_timed (P : X3DHParams W)
    (A : KI_Adversary P) (sk : W) (keygen : SPTree.Timed (W × W))
    (run : W → X3DHTranscript W → SPTree.Timed Bool) (runCost : W → X3DHTranscript W → ℕ)
    {Tk T a : ℕ} (hk : keygen.time ≤ Tk) (hA : ∀ x y, (run x y).time ≤ T)
    (hAc : ∀ x y, runCost x y ≤ a) :
    SPTree.Timed.stepTime (kdfReduction.tree.timed P A sk keygen run runCost) ≤
      5 * Tk + T + a + 1 := by
  time_bound
/-- **Time of the hop-2 reduction over key generation**: four key generations, two ECDH
calls, the KDF and the adversary. -/
theorem ddhRedK2.tree.timeBound_timed (P : X3DHParams W)
    (A : KI_Adversary P) (g_a g_b z : W)
    (kdf : W → W → W → W → W) (kdfCost : W → W → W → W → ℕ)
    (ecdh : W → W → W) (ecdhCost : W → W → ℕ) (keygen : SPTree.Timed (W × W))
    (run : W → X3DHTranscript W → SPTree.Timed Bool) (runCost : W → X3DHTranscript W → ℕ)
    {Tk T a c e : ℕ} (hk : keygen.time ≤ Tk) (hA : ∀ x y, (run x y).time ≤ T)
    (hAc : ∀ x y, runCost x y ≤ a) (hc : ∀ w₁ w₂ w₃ w₄, kdfCost w₁ w₂ w₃ w₄ ≤ c)
    (he : ∀ w₁ w₂, ecdhCost w₁ w₂ ≤ e) :
    SPTree.Timed.stepTime (ddhRedK2.tree.timed P A g_a g_b z kdf kdfCost ecdh ecdhCost keygen
      run runCost) ≤ 4 * Tk + T + a + c + 2 * e + 4 := by
  time_bound
/-- **Time of the hop-3 reduction over key generation**: five key generations, one ECDH call,
the KDF and the adversary. -/
theorem ddhRedK3.tree.timeBound_timed (P : X3DHParams W)
    (A : KI_Adversary P) (g_a g_b z : W)
    (kdf : W → W → W → W → W) (kdfCost : W → W → W → W → ℕ)
    (ecdh : W → W → W) (ecdhCost : W → W → ℕ) (keygen : SPTree.Timed (W × W))
    (run : W → X3DHTranscript W → SPTree.Timed Bool) (runCost : W → X3DHTranscript W → ℕ)
    {Tk T a c e : ℕ} (hk : keygen.time ≤ Tk) (hA : ∀ x y, (run x y).time ≤ T)
    (hAc : ∀ x y, runCost x y ≤ a) (hc : ∀ w₁ w₂ w₃ w₄, kdfCost w₁ w₂ w₃ w₄ ≤ c)
    (he : ∀ w₁ w₂, ecdhCost w₁ w₂ ≤ e) :
    SPTree.Timed.stepTime (ddhRedK3.tree.timed P A g_a g_b z kdf kdfCost ecdh ecdhCost keygen
      run runCost) ≤ 5 * Tk + T + a + c + e + 4 := by
  time_bound
/-- **Time of the hop-4 reduction over key generation**: six key generations, the KDF and the
adversary. -/
theorem ddhRedK4.tree.timeBound_timed (P : X3DHParams W)
    (A : KI_Adversary P) (g_a g_b z : W)
    (kdf : W → W → W → W → W) (kdfCost : W → W → W → W → ℕ) (keygen : SPTree.Timed (W × W))
    (run : W → X3DHTranscript W → SPTree.Timed Bool) (runCost : W → X3DHTranscript W → ℕ)
    {Tk T a c : ℕ} (hk : keygen.time ≤ Tk) (hA : ∀ x y, (run x y).time ≤ T)
    (hAc : ∀ x y, runCost x y ≤ a) (hc : ∀ w₁ w₂ w₃ w₄, kdfCost w₁ w₂ w₃ w₄ ≤ c) :
    SPTree.Timed.stepTime (ddhRedK4.tree.timed P A g_a g_b z kdf kdfCost keygen run runCost) ≤
      6 * Tk + T + a + c + 4 := by
  time_bound
end CatCrypt.Crypto.Signal.Session.X3DHHops
