/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCConcrete

/-!
# Concrete UC emulation with a leak-then-simulate simulator

A real game `Gr : hon → SPComp leak` emulates an ideal functionality `F : hon → SPComp L` whose
leakage `L` differs from the real adversary's view `leak`, through the simulator that runs a
simulation `Sb : L → SPComp leak` on the ideal leakage and hands the result to the adversary.
The bound is a concrete game bound between `Gr` and the composite game `F >=> Sb`.

## Main results

* `UCEmulatesCSim_of_isPure_simGame` — heap-independent `Gr`, `F`, `Sb` and a bound on the
  advantage between `Gr x` and `(F x).bind Sb` give `UCEmulatesCSim` with the simulator
  `fun A l => (Sb l).bind A` and the bound `gameUCBound bound`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCConcrete

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCDSL CatCrypt.Crypto.UCComposition
open scoped ENNReal

/-- Concrete UC emulation of an ideal game `F` by a real game `Gr` with the simulator that runs
`Sb` on the ideal leakage and passes its output to the adversary. The bound is the game bound
between `Gr x` and the composite `(F x).bind Sb`, at the environment's input and the
distinguisher `envReduction A Z`. -/
theorem UCEmulatesCSim_of_isPure_simGame {hon leak L V : Type}
    {Gr : hon → SPComp leak} {F : hon → SPComp L} {Sb : L → SPComp leak}
    {bound : hon → (leak → SPComp Bool) → ℝ≥0∞}
    (hr : ∀ x, SPComp.IsPure (Gr x)) (hF : ∀ x, SPComp.IsPure (F x))
    (hS : ∀ l, SPComp.IsPure (Sb l))
    (hAdv : ∀ x D, AdvantageA (Gr x) ((F x).bind Sb) D ≤ bound x D) :
    UCEmulatesCSim ⟨hon, Unit, leak, L, V⟩ (UCProtocol.ofGame Gr) (UCProtocol.ofGame F)
      (fun A l => (Sb l).bind A) (gameUCBound bound) := by
  intro A Z
  have h := DistC_of_isPure_advantageA hr (fun x => SPComp.bind_isPure (hF x) hS) hAdv
    ⟨Z.input, Z.heap, fun o => SPComp.bind (A o) (fun v => Z.dist (.inr v))⟩
  change absDiff
      (prTrue (SPComp.bind (SPComp.bind (UCProtocol.ofGame Gr Z.input)
        (mapSum SPComp.pure A)) Z.dist) Z.heap)
      (prTrue (SPComp.bind (SPComp.bind (UCProtocol.ofGame F Z.input)
        (mapSum SPComp.pure fun l => (Sb l).bind A)) Z.dist) Z.heap) ≤ _
  rw [ofGame_run_eq, ofGame_run_eq]
  simp only [SPComp.bind_assoc]
  rw [← SPComp.bind_assoc (F Z.input) Sb (fun o => SPComp.bind (A o) (fun v => Z.dist (.inr v)))]
  exact h

end CatCrypt.Crypto.UCConcrete
