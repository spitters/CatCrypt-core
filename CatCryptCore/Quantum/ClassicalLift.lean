/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.ClassicalEmbed
public import CatCryptCore.Crypto.UCMonad.QuantumUC
public import CatCryptCore.Core.Code

/-!
# Classical-to-Quantum Distance Lifting

Theorems transporting statistical-distance bounds on classical computations
(over `SDistr`) to distinguishing-distance bounds on their embeddings in
`QComp d` via `classicalEmbed`.

## Main Results

* `classical_to_quantum_uc_lift` — `sdistD f g ≤ ε → qdist (classicalEmbed ∘ f) (classicalEmbed ∘ g) ≤ ε`
* `quantum_uc_of_eq` — when real = ideal, quantum distance is 0
* `quantum_lift_spcomp` — lift SPComp protocols via `Heap.empty` evaluation
* `PQGameAdvantage` — the quantum-distinguisher advantage against a classical
  Boolean game, as `qdist` of its embedded arms
* `absDiffD_prTrueD_le_sdistD` — the accept-probability gap of a Boolean game
  is bounded by the statistical distance of its arms

## Statement

`classical_to_quantum_uc_lift` rests on `classicalEmbed_sdist_eq`, which equates
the classical statistical distance with the distance seen by quantum
distinguishers that post-process the classical outputs:

```
sdistD f g = qdist (classicalEmbed ∘ f) (classicalEmbed ∘ g)
```

The embedded computations act on the quantum state only through the classical
outcome probabilities; quantum access to `f` or `g` in superposition is not
modelled.

## References

* [Unruh — Quantum Proofs of Knowledge, EUROCRYPT 2012]
-/

@[expose] public section

open scoped ENNReal
open CatCrypt.Prob CatCrypt.Quantum UCMonad.QuantumUC UCMonad.SDistrUC

namespace CatCrypt.Quantum.ClassicalLift

variable {d : ℕ} {α β : Type}

/-! ## Core Lifting Theorems -/

/-- **Classical-to-quantum distance lifting.**

    If `sdistD f g ≤ ε`, then
    `qdist (classicalEmbed ∘ f) (classicalEmbed ∘ g) ≤ ε`: quantum
    distinguishers that post-process the classical outputs gain nothing over
    classical ones (`classicalEmbed_sdist_eq`).

    Requires `[NeZero d]` (nonzero Hilbert space dimension). -/
theorem classical_to_quantum_uc_lift [NeZero d]
    {ε : ℝ≥0∞}
    (f g : α → SDistr β)
    (h_cl : sdistD f g ≤ ε) :
    qdist (fun a => classicalEmbed (f a) : α → QComp d β)
          (fun a => classicalEmbed (g a)) ≤ ε := by
  rw [← classicalEmbed_sdist_eq]
  exact h_cl

/-- When two classical protocols are equal, their quantum embeddings have
    distance 0. No ε needed. -/
theorem quantum_uc_of_eq [NeZero d]
    (f g : α → SDistr β)
    (h : f = g) :
    qdist (fun a => classicalEmbed (f a) : α → QComp d β)
          (fun a => classicalEmbed (g a)) = 0 := by
  subst h; rw [← classicalEmbed_sdist_eq]; exact sdistD_self f

/-- Convenience: lift SPComp protocols to quantum by evaluating at `Heap.empty`.

    Most protocols are `hon → SPComp out`, i.e., `hon → Heap → SDistr (out × Heap)`.
    This theorem applies `Heap.empty` to get `hon → SDistr (out × Heap)`, then lifts
    to quantum. -/
theorem quantum_lift_spcomp [NeZero d]
    {ε : ℝ≥0∞}
    (f g : α → CatCrypt.Core.SPComp β)
    (h : sdistD (fun a => f a CatCrypt.Core.Heap.empty)
                (fun a => g a CatCrypt.Core.Heap.empty) ≤ ε) :
    qdist (fun a => classicalEmbed (f a CatCrypt.Core.Heap.empty) : α → QComp d _)
          (fun a => classicalEmbed (g a CatCrypt.Core.Heap.empty)) ≤ ε :=
  classical_to_quantum_uc_lift _ _ h

/-- When two SPComp protocols are equal, their quantum lift has distance 0. -/
theorem quantum_lift_spcomp_of_eq [NeZero d]
    (f g : α → CatCrypt.Core.SPComp β)
    (h : f = g) :
    qdist (fun a => classicalEmbed (f a CatCrypt.Core.Heap.empty) : α → QComp d _)
          (fun a => classicalEmbed (g a CatCrypt.Core.Heap.empty)) = 0 := by
  subst h
  exact quantum_uc_of_eq _ _ rfl

/-! ## Classical Boolean games against quantum distinguishers -/

/-- The advantage of the best quantum distinguisher `D : Bool → QComp d Bool`,
evaluated on an arbitrary auxiliary state `ρ`, against the two arms of a
classical Boolean game `G`, each embedded as a quantum instrument. It is
`UCMonad.QuantumUC.qdist` of the embedded arms:

```
⨆ (D) (a) (ρ), absDiff (prTrue_Q (classicalEmbed (G a true)  >>= D) ρ)
                        (prTrue_Q (classicalEmbed (G a false) >>= D) ρ)
```

By `classicalEmbed_sdist_eq` it equals the classical statistical distance
`sdistD (fun a => G a true) (fun a => G a false)` when `d ≠ 0`. -/
noncomputable def PQGameAdvantage (d : ℕ) {α : Type} (G : α → Bool → SDistr Bool) :
    ℝ≥0∞ :=
  qdist (fun a => (classicalEmbed (G a true) : QComp d Bool))
        (fun a => classicalEmbed (G a false))

/-- A game whose two arms coincide has post-quantum advantage zero. -/
theorem pqGameAdvantage_diag (G : α → SDistr Bool) :
    PQGameAdvantage d (fun a _ => G a) = 0 :=
  qdist_self _

/-- The accept-probability gap of a Boolean game is bounded by the
statistical distance of its two arms: it is the identity-continuation
instance of the distinguisher supremum. -/
theorem absDiffD_prTrueD_le_sdistD (G : Bool → SDistr Bool) :
    absDiffD (prTrueD (G true)) (prTrueD (G false))
      ≤ sdistD (fun _ : Unit => G true) (fun _ : Unit => G false) := by
  calc absDiffD (prTrueD (G true)) (prTrueD (G false))
      = absDiffD (prTrueD ((G true).bind SDistr.pure))
                 (prTrueD ((G false).bind SDistr.pure)) := by
        rw [SDistr.bind_pure, SDistr.bind_pure]
    _ ≤ _ := le_iSup₂_of_le (SDistr.pure : Bool → SDistr Bool) () le_rfl

end CatCrypt.Quantum.ClassicalLift
