/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.AdversariesTimed
public import CatCryptCore.Tactics.DeriveReduction

/-!
# Time certificate of the query-prefix reduction of `QOwcpaAux`

The costed form `owRedQuery.timed` of the reduction `owRedQuery` from a KEM adversary to a
one-wayness adversary with oracle access, derived by `derive_reduction`, with its erasure
theorem `owRedQuery.erase_timed`. The reduction runs the multi-round circuit of the KEM
adversary unchanged, so its time is that of the adversary plus a constant.

## Main results

* `owRedQuery.timeBound` — the time of the reduction is the time of the KEM adversary plus `2`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.QROM

derive_reduction owRedQuery

/-- **Time of `owRedQuery`.** If every circuit of the costed KEM adversary, with the cost of
computing it, runs within `T`, then every circuit of the reduction runs within `T + 2`. -/
theorem owRedQuery.timeBound {m₁ m₂ n w q k c a : ℕ} {PK C K : Type}
    (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (run : PK → C → K → QAdvMRT (m₁ + m₂) n (2 * w) q k c a) (runCost : PK → C → K → ℕ)
    (T : ℕ) (hT : ∀ pk cst h, QAdvMRT.StepTimeBound (runCost pk cst h, run pk cst h) T) :
    (owRedQuery.timed A b run runCost).TimeBound (T + 2) := by
  intro pk cst h x
  have := hT pk cst (if b = true then h else x.1)
  simp only [QAdvMRT.StepTimeBound, owRedQuery.timed, owRedQuery.prog.tree.timed] at *
  omega

end CatCrypt.Quantum.QROM
