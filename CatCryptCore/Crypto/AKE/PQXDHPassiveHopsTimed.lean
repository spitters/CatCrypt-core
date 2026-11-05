/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHPassiveHops
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Costed forms of the PQXDH hop reductions

`derive_reduction` reflects the KEM reduction `kemRed`, the DDH reductions `ddhRed1` …
`ddhRed4` and the KDF reduction `kdfReduction` of `PQXDHPassiveHops` into computation trees and
derives their costed forms `R.tree.timed`, with the compilation theorems `R.compile_tree` and
the erasure theorems `R.tree.erase_timed`. The primitives of a reduction (the key generation,
the ECDH function, the KEM functions, the KDF and the adversary's `run`) are parameters of its
costed tree with their cost companions.

## Main results

With key generation of time at most `Tk`, the adversary's `run` of time at most `T` and call
cost at most `a`, the KDF of cost at most `c`, the ECDH function of cost at most `e`, KEM key
generation of cost at most `g` and encapsulation of cost at most `u`:

* `kemRed.tree.timeBound_timed` — time at most `5 * Tk + T + a + c + 4 * e + 6`;
* `ddhRed1.tree.timeBound_timed` — time at most `3 * Tk + T + a + c + 3 * e + 2 * g + u + 11`;
* `ddhRed2.tree.timeBound_timed` — time at most `3 * Tk + T + a + c + 2 * e + 2 * g + u + 11`;
* `ddhRed3.tree.timeBound_timed` — time at most `3 * Tk + T + a + c + e + 2 * g + u + 11`;
* `ddhRed4.tree.timeBound_timed` — time at most `3 * Tk + T + a + c + 2 * g + u + 11`;
* `kdfReduction.tree.timeBound_timed` — time at most `5 * Tk + T + a + 2 * g + u + 6`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.PQXDHPassive

open CatCrypt.Core

derive_reduction kemRed

derive_reduction ddhRed1

derive_reduction ddhRed2

derive_reduction ddhRed3

derive_reduction ddhRed4

derive_reduction kdfReduction

variable {W PK SK C Sd : Type} [SampleableType W] [SampleableType Sd]

omit [SampleableType Sd] in
/-- **Time of the hop-0 reduction**: five key generations of time at most `Tk`, four ECDH
calls of cost at most `e`, the KDF of cost at most `c` and the adversary of time `T` and call
cost `a`. -/
theorem kemRed.tree.timeBound_timed (P : PassiveParams W PK SK C Sd)
    (A : KI_Adversary P) (pk : PK) (ct : C) (k : W)
    (kdf : W → W → W → W → W → W) (kdfCost : W → W → W → W → W → ℕ)
    (ecdh : W → W → W) (ecdhCost : W → W → ℕ) (keygen : SPTree.Timed (W × W))
    (run : W → PQXDHTranscript W PK C → SPTree.Timed Bool)
    (runCost : W → PQXDHTranscript W PK C → ℕ)
    {Tk T a c e : ℕ} (hk : keygen.time ≤ Tk) (hA : ∀ x y, (run x y).time ≤ T)
    (hAc : ∀ x y, runCost x y ≤ a) (hc : ∀ w₁ w₂ w₃ w₄ w₅, kdfCost w₁ w₂ w₃ w₄ w₅ ≤ c)
    (he : ∀ w₁ w₂, ecdhCost w₁ w₂ ≤ e) :
    SPTree.Timed.stepTime (kemRed.tree.timed P A pk ct k kdf kdfCost ecdh ecdhCost keygen
      run runCost) ≤ 5 * Tk + T + a + c + 4 * e + 6 := by
  time_bound
/-- **Time of the hop-1 reduction**: three key generations, three ECDH calls, three uniform
samples, the KEM functions, the KDF and the adversary. -/
theorem ddhRed1.tree.timeBound_timed (P : PassiveParams W PK SK C Sd)
    (A : KI_Adversary P) (g_a g_b z : W)
    (kdf : W → W → W → W → W → W) (kdfCost : W → W → W → W → W → ℕ)
    (ecdh : W → W → W) (ecdhCost : W → W → ℕ)
    (kemKeygen : Sd → PK × SK) (kemKeygenCost : Sd → ℕ)
    (kemEncaps : PK → W → C × W) (kemEncapsCost : PK → W → ℕ) (keygen : SPTree.Timed (W × W))
    (run : W → PQXDHTranscript W PK C → SPTree.Timed Bool)
    (runCost : W → PQXDHTranscript W PK C → ℕ)
    {Tk T a c g u e : ℕ} (hk : keygen.time ≤ Tk) (hA : ∀ x y, (run x y).time ≤ T)
    (hAc : ∀ x y, runCost x y ≤ a) (hc : ∀ w₁ w₂ w₃ w₄ w₅, kdfCost w₁ w₂ w₃ w₄ w₅ ≤ c)
    (he : ∀ w₁ w₂, ecdhCost w₁ w₂ ≤ e)
    (hg : ∀ sd, kemKeygenCost sd ≤ g) (hu : ∀ pk m, kemEncapsCost pk m ≤ u) :
    SPTree.Timed.stepTime (ddhRed1.tree.timed P A g_a g_b z kdf kdfCost ecdh ecdhCost kemKeygen
      kemKeygenCost kemEncaps kemEncapsCost keygen run runCost) ≤
      3 * Tk + T + a + c + 3 * e + 2 * g + u + 11 := by
  time_bound
/-- **Time of the hop-2 reduction**: three key generations, four uniform samples, two ECDH
calls, the KEM functions, the KDF and the adversary. -/
theorem ddhRed2.tree.timeBound_timed (P : PassiveParams W PK SK C Sd)
    (A : KI_Adversary P) (g_a g_b z : W)
    (kdf : W → W → W → W → W → W) (kdfCost : W → W → W → W → W → ℕ)
    (ecdh : W → W → W) (ecdhCost : W → W → ℕ)
    (kemKeygen : Sd → PK × SK) (kemKeygenCost : Sd → ℕ)
    (kemEncaps : PK → W → C × W) (kemEncapsCost : PK → W → ℕ) (keygen : SPTree.Timed (W × W))
    (run : W → PQXDHTranscript W PK C → SPTree.Timed Bool)
    (runCost : W → PQXDHTranscript W PK C → ℕ)
    {Tk T a c g u e : ℕ} (hk : keygen.time ≤ Tk) (hA : ∀ x y, (run x y).time ≤ T)
    (hAc : ∀ x y, runCost x y ≤ a) (hc : ∀ w₁ w₂ w₃ w₄ w₅, kdfCost w₁ w₂ w₃ w₄ w₅ ≤ c)
    (he : ∀ w₁ w₂, ecdhCost w₁ w₂ ≤ e)
    (hg : ∀ sd, kemKeygenCost sd ≤ g) (hu : ∀ pk m, kemEncapsCost pk m ≤ u) :
    SPTree.Timed.stepTime (ddhRed2.tree.timed P A g_a g_b z kdf kdfCost ecdh ecdhCost kemKeygen
      kemKeygenCost kemEncaps kemEncapsCost keygen run runCost) ≤
      3 * Tk + T + a + c + 2 * e + 2 * g + u + 11 := by
  time_bound
/-- **Time of the hop-3 reduction**: three key generations, five uniform samples, one ECDH
call, the KEM functions, the KDF and the adversary. -/
theorem ddhRed3.tree.timeBound_timed (P : PassiveParams W PK SK C Sd)
    (A : KI_Adversary P) (g_a g_b z : W)
    (kdf : W → W → W → W → W → W) (kdfCost : W → W → W → W → W → ℕ)
    (ecdh : W → W → W) (ecdhCost : W → W → ℕ)
    (kemKeygen : Sd → PK × SK) (kemKeygenCost : Sd → ℕ)
    (kemEncaps : PK → W → C × W) (kemEncapsCost : PK → W → ℕ) (keygen : SPTree.Timed (W × W))
    (run : W → PQXDHTranscript W PK C → SPTree.Timed Bool)
    (runCost : W → PQXDHTranscript W PK C → ℕ)
    {Tk T a c g u e : ℕ} (hk : keygen.time ≤ Tk) (hA : ∀ x y, (run x y).time ≤ T)
    (hAc : ∀ x y, runCost x y ≤ a) (hc : ∀ w₁ w₂ w₃ w₄ w₅, kdfCost w₁ w₂ w₃ w₄ w₅ ≤ c)
    (he : ∀ w₁ w₂, ecdhCost w₁ w₂ ≤ e)
    (hg : ∀ sd, kemKeygenCost sd ≤ g) (hu : ∀ pk m, kemEncapsCost pk m ≤ u) :
    SPTree.Timed.stepTime (ddhRed3.tree.timed P A g_a g_b z kdf kdfCost ecdh ecdhCost kemKeygen
      kemKeygenCost kemEncaps kemEncapsCost keygen run runCost) ≤
      3 * Tk + T + a + c + e + 2 * g + u + 11 := by
  time_bound
/-- **Time of the hop-4 reduction**: three key generations, six uniform samples, the KEM
functions, the KDF and the adversary. -/
theorem ddhRed4.tree.timeBound_timed (P : PassiveParams W PK SK C Sd)
    (A : KI_Adversary P) (g_a g_b z : W)
    (kdf : W → W → W → W → W → W) (kdfCost : W → W → W → W → W → ℕ)
    (kemKeygen : Sd → PK × SK) (kemKeygenCost : Sd → ℕ)
    (kemEncaps : PK → W → C × W) (kemEncapsCost : PK → W → ℕ) (keygen : SPTree.Timed (W × W))
    (run : W → PQXDHTranscript W PK C → SPTree.Timed Bool)
    (runCost : W → PQXDHTranscript W PK C → ℕ)
    {Tk T a c g u : ℕ} (hk : keygen.time ≤ Tk) (hA : ∀ x y, (run x y).time ≤ T)
    (hAc : ∀ x y, runCost x y ≤ a) (hc : ∀ w₁ w₂ w₃ w₄ w₅, kdfCost w₁ w₂ w₃ w₄ w₅ ≤ c)
    (hg : ∀ sd, kemKeygenCost sd ≤ g) (hu : ∀ pk m, kemEncapsCost pk m ≤ u) :
    SPTree.Timed.stepTime (ddhRed4.tree.timed P A g_a g_b z kdf kdfCost kemKeygen
      kemKeygenCost kemEncaps kemEncapsCost keygen run runCost) ≤
      3 * Tk + T + a + c + 2 * g + u + 11 := by
  time_bound
/-- **Time of the KDF reduction**: five key generations, two uniform samples, the KEM
functions and the adversary. -/
theorem kdfReduction.tree.timeBound_timed (P : PassiveParams W PK SK C Sd)
    (A : KI_Adversary P) (sk : W)
    (kemKeygen : Sd → PK × SK) (kemKeygenCost : Sd → ℕ)
    (kemEncaps : PK → W → C × W) (kemEncapsCost : PK → W → ℕ) (keygen : SPTree.Timed (W × W))
    (run : W → PQXDHTranscript W PK C → SPTree.Timed Bool)
    (runCost : W → PQXDHTranscript W PK C → ℕ)
    {Tk T a g u : ℕ} (hk : keygen.time ≤ Tk) (hA : ∀ x y, (run x y).time ≤ T)
    (hAc : ∀ x y, runCost x y ≤ a) (hg : ∀ sd, kemKeygenCost sd ≤ g)
    (hu : ∀ pk m, kemEncapsCost pk m ≤ u) :
    SPTree.Timed.stepTime (kdfReduction.tree.timed P A sk kemKeygen kemKeygenCost kemEncaps
      kemEncapsCost keygen run runCost) ≤ 5 * Tk + T + a + 2 * g + u + 6 := by
  time_bound

end CatCrypt.Crypto.Signal.PQXDHPassive
