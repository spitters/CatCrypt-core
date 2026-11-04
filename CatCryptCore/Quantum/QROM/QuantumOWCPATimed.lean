/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.AdversariesTimed
public import CatCryptCore.Tactics.DeriveReduction

/-!
# Time certificate of the absorbing reduction of `QuantumOWCPA`

The costed form `tReduction.timed` of the reduction `tReduction` from a `TAdv` to a quantum
OW-CPA adversary, derived by `derive_reduction`, with its erasure theorem
`tReduction.erase_timed`. At each oracle table `G` the reduction absorbs the oracle into the
circuit of the adversary (`QAdvT.absorb`): each oracle call becomes one gate of weight one, so
the time is that of the adversary plus a constant.

## Main results

* `tReduction.timeBound` — the time of the reduction is the time of the adversary plus `1`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.QROM

derive_reduction tReduction

/-- **Time of `tReduction`.** If every circuit of the costed `TAdv`, with the cost of computing
it, runs within `T`, then every circuit of the reduction runs within `T + 1`. -/
theorem tReduction.timeBound {m n w q : ℕ} {PK M C R : Type} [Fintype M] [Fintype R]
    [Nonempty R] (eM : M ≃ Fin m) (eR : R ≃ Fin n) [NeZero n] (A : TAdv m n w q PK C)
    (run : PK → C → Fin m → QAdvT m n (m * w) q) (runCost : PK → C → Fin m → ℕ) (T : ℕ)
    (h : ∀ pk cst x, QAdvT.StepTimeBound (runCost pk cst x, run pk cst x) T) :
    (tReduction.timed eM eR A run runCost).TimeBound (T + 1) := by
  intro (G : Fin m → Fin n) pk cst x
  have := h pk cst x
  simp only [QAdvT.StepTimeBound, tReduction.timed, tReduction.run.tree.timed] at *
  rw [QAdvT.time_absorb]
  omega

end CatCrypt.Quantum.QROM
