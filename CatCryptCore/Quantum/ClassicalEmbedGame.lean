/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.ClassicalEmbed
public import CatCryptCore.Crypto.SDist

/-!
# Quantum distinguishers of classically embedded games

A quantum distinguisher of the classically embedded output of an `SPComp` game run from
the empty heap accepts with the probability of a classical distinguisher
(`quantum_classical_simulation`). This module states that correspondence for game pairs.
It is separate from `ClassicalEmbed` so that the importers of the embedding do not load
the game layer.

## Main results

* `ofSDistrHeapDist` — the `SPComp` distinguisher running a sub-distribution
  distinguisher on the output and the final heap of a game
* `exists_advantageA_eq_quantum_gap` — a quantum distinguisher of embedded game outputs
  has the advantage of one classical distinguisher on every pair of games
* `quantum_gap_le_of_advantage` — a classical advantage bound bounds the quantum gap
-/

@[expose] public section

open scoped Matrix ComplexOrder ENNReal Matrix.Norms.Elementwise
open Matrix Classical CatCrypt.Prob CatCrypt.Quantum
open UCMonad.QuantumUC UCMonad.SDistrUC

noncomputable section

namespace CatCrypt.Quantum

variable {d : ℕ} {β : Type}

/-! ## Quantum distinguishers of embedded game outputs -/

section GameDistinguisher

open CatCrypt.Core
open CatCrypt.Crypto (prTrue Advantage AdvantageA prTrue_bind_eq_weighted)

/-- The `SPComp` distinguisher running the sub-distribution distinguisher `D` on the
output and the current heap, with the heap unchanged. -/
noncomputable def ofSDistrHeapDist (D : β × Heap → SDistr Bool) : β → SPComp Bool :=
  fun b h => (D (b, h)).map (Option.map fun x => (x, h))

/-- A sub-distribution distinguisher `D` on the run of a game from the empty heap accepts
with the probability of the `SPComp` distinguisher `ofSDistrHeapDist D` on that game. -/
theorem prTrueD_bind_eq_prTrue_bind (G : SPComp β) (D : β × Heap → SDistr Bool) :
    prTrueD (SDistr.bind (G Heap.empty) D) =
      prTrue (G.bind (ofSDistrHeapDist D)) Heap.empty := by
  have hstep : ∀ (b : β) (h' : Heap),
      prTrue (ofSDistrHeapDist D b) h' = D (b, h') (some true) := by
    intro b h'
    rw [prTrue, ofSDistrHeapDist, tsum_eq_single h' fun h hh => ?_]
    · rw [PMF.map_apply, tsum_eq_single (some true) fun o ho => ?_]
      · simp
      · rcases o with _ | _ <;> simp_all
    · rw [PMF.map_apply]
      simp [Ne.symm hh]
  rw [prTrue_bind_eq_weighted, prTrueD, SDistr.bind, PMF.bind_apply]
  refine tsum_congr fun p => ?_
  rcases p with _ | ⟨b, h'⟩
  · simp [SDistr.fail]
  · exact congrArg _ (hstep b h').symm

/-- For a quantum distinguisher `D_Q` and a state `ρ` there is one classical distinguisher
`A` such that, for any two games, the gap between the probabilities with which `D_Q`
accepts their embedded outputs from the empty heap is the advantage of `A` between them. -/
theorem exists_advantageA_eq_quantum_gap (D_Q : β × Heap → QComp d Bool)
    (ρ : DensityMatrix d) :
    ∃ A : β → SPComp Bool, ∀ G₀ G₁ : SPComp β,
      absDiff (prTrue_Q (QComp.qbind (classicalEmbed (G₀ Heap.empty)) D_Q) ρ)
          (prTrue_Q (QComp.qbind (classicalEmbed (G₁ Heap.empty)) D_Q) ρ) =
        AdvantageA G₀ G₁ A := by
  obtain ⟨D_cl, hD⟩ := quantum_classical_simulation D_Q ρ
  refine ⟨ofSDistrHeapDist D_cl, fun G₀ G₁ => ?_⟩
  rw [hD, hD, prTrueD_bind_eq_prTrue_bind, prTrueD_bind_eq_prTrue_bind]
  simp only [AdvantageA, Advantage, absDiff]

/-- A bound on the advantage of every classical distinguisher between two games bounds
the gap with which a quantum distinguisher accepts their embedded outputs, at the
classical distinguisher of `exists_advantageA_eq_quantum_gap`. -/
theorem quantum_gap_le_of_advantage (G₀ G₁ : SPComp β) (bound : (β → SPComp Bool) → ℝ≥0∞)
    (hb : ∀ A : β → SPComp Bool, AdvantageA G₀ G₁ A ≤ bound A)
    (D_Q : β × Heap → QComp d Bool) (ρ : DensityMatrix d) :
    ∃ A : β → SPComp Bool,
      absDiff (prTrue_Q (QComp.qbind (classicalEmbed (G₀ Heap.empty)) D_Q) ρ)
          (prTrue_Q (QComp.qbind (classicalEmbed (G₁ Heap.empty)) D_Q) ρ) ≤ bound A := by
  obtain ⟨A, hA⟩ := exists_advantageA_eq_quantum_gap D_Q ρ
  exact ⟨A, (hA G₀ G₁).trans_le (hb A)⟩

end GameDistinguisher

end CatCrypt.Quantum
