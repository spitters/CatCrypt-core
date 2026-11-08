/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.AdversariesTimed
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.StdCosts

/-!
# Time certificate of the IND-CPA reduction of `QIndcpaAux`

The costed form `indRed.timed` of the reduction `indRed` from a one-wayness adversary with
oracle access to an IND-CPA adversary with oracle access, derived by `derive_reduction`, with
its erasure theorem `indRed.erase_timed`. The reduction runs the multi-round circuit of the
one-wayness adversary unchanged, so its time is that of the adversary plus a constant.

## Main results

* `indRed.timeBound` — the time of the reduction is the time of the adversary plus `1`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.QROM

derive_reduction indRed

/-- **Time of `indRed`.** If every circuit of the costed one-wayness adversary, with the cost
of computing it, runs within `T`, then every circuit of the reduction runs within `T + 1`. -/
theorem indRed.timeBound {m₁ m₂ n W q k c a : ℕ} {PK M C K Hash ι : Type} [Nonempty M]
    (eG : M × Hash ≃ Fin m₁) [DecidableEq M] (B : QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K)
    (prog : PK → C → K → ι → QAdvMRT (m₁ + m₂) n W q k c a)
    (progCost : PK → C → K → ι → ℕ) (T : ℕ)
    (hT : ∀ pk cst h i, QAdvMRT.StepTimeBound (progCost pk cst h i, prog pk cst h i) T) :
    (indRed.timed eG B prog progCost).TimeBound (T + 1) := by
  intro pk cst h x
  have := hT pk cst h x.2.2
  simp only [QAdvMRT.StepTimeBound, indRed.timed, indRed.prog.tree.timed] at *
  omega

end CatCrypt.Quantum.QROM
