/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.HopChallengeKey
public import CatCryptCore.Quantum.QROM.FindToGuess

/-!
# The challenge point of the merged oracle and the OW-CPA register

The guessing step of `Quantum/QROM/FindToGuess.lean` turns the averaged
probability that a measured query lands in the punctured set into the quantum
OW-CPA advantage of a reduction. For the KEM adversary of
`Quantum/QROM/KEMQuantumGame.lean` that step needs two pieces: a map from the
challenge point of the merged oracle back to a message index, and an embedding
of the KEM adversary's register into the register a `QOWAdv` measures. This
module supplies the first and shows that the second does not exist for
`QOWAdv` as stated.

## Main definitions

* `kemPtMsg m₁ m₂` — the partial inverse of the left tagging
  `Fin.castAdd m₂ : Fin m₁ → Fin (m₁ + m₂)`
* `kemPtMerged hpk eG i` — the challenge point `kemPt hpk eG i` tagged into the
  left summand of `Fin (m₁ + m₂)`

## Main results

* `kemPtMsg_castAdd`, `kemPtMsg_natAdd`, `kemPtMsg_eq_some_iff` — the map
  inverts the left tagging and is `none` on the right summand
* `mergeSet_kemPt_eq_singleton` — the punctured set of the challenge-key hop is
  the singleton `{kemPtMerged hpk eG i}`
* `kemPtMsg_kemPtMerged` — the map sends the tagged challenge point to
  `some (eG (m*, hpk pk))`
* `kemPt_inj` — the challenge point determines the pair `(m*, hpk pk)`
* `trace_projS_singleton`, `trace_winProj` — the traces of the two projectors
* `owcpa_register_forces_domain_eq` — dimension and trace equalities force the
  oracle domain of the adversary to equal the message-index range of the
  `QOWAdv`
* `owcpa_embedding_obstruction` — a unitary carrying a rank-`n · W` projector to
  `winProj m n w' x` forces the same equality
* `kem_owcpa_index_mismatch` — that equality holds only when `Hash` is a
  singleton and the second oracle summand is empty

## Scope

The point map is unconditional: it is the `Fin.addCases` inverse of the left
tagging, and the singleton identification of the hop's punctured set is an
identity of `Finset`s.

The register embedding is not constructed. `QOWAdv m n w PK C` of
`Quantum/QROM/QuantumOWCPA.lean` identifies three index ranges: the oracle
domain, the target-message range of `run`, and the output factor of the work
register `Fin (m * w)`, on which `final_eq` pins the final projector to
`winProj m n w x`. `qOwcpaAdvantage P eM` applies `run` at `eM x` with
`eM : M ≃ Fin m`, so `m = Fintype.card M`. The KEM adversary's oracle domain is
`Fin (m₁ + m₂)` with `eG : M × Hash ≃ Fin m₁` and `eJ : Z × C ≃ Fin m₂`, and its
work register is `ancW c k (2 * w)`, which carries no factor of the oracle
domain. `owcpa_embedding_obstruction` states the consequence of an embedding
that is a permutation of the index type: equal total dimension and, since a
unitary conjugation preserves the trace, equal projector trace. Together these
give `m₁ + m₂ = m`, which by `kem_owcpa_index_mismatch` holds only when
`Fintype.card Hash = 1` and `m₂ = 0`.

A formulation of the OW-CPA adversary that would admit the embedding has to
separate the three ranges: an oracle domain `Fin d`, a target-message range
`Fin m` with an injection `Fin m → Fin d` recording where the challenge point
sits, a work register `Fin W` unconstrained by `d`, and a final projector read
off the measured query register rather than an output factor of the work
register — that is, `projS d n W {t}` in place of `winProj m n w x`, with the
win condition `kemPtMsg` of the measured query equalling the target index. With
the projector on the query register, the swap of `FindToGuess.swapU` is not
needed and the prefix adversary is already the required `0`-query adversary.

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], Theorem 2
* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.2
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal

open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The challenge point as a message index -/

section PointMap

variable {m₁ m₂ : ℕ}

/-- The partial inverse of the left tagging: `some x` on `Fin.castAdd m₂ x` and
    `none` on the second summand. -/
def kemPtMsg (m₁ m₂ : ℕ) : Fin (m₁ + m₂) → Option (Fin m₁) :=
  Fin.addCases (motive := fun _ => Option (Fin m₁)) some fun _ => none

@[simp]
theorem kemPtMsg_castAdd (x : Fin m₁) : kemPtMsg m₁ m₂ (Fin.castAdd m₂ x) = some x :=
  Fin.addCases_left x

@[simp]
theorem kemPtMsg_natAdd (y : Fin m₂) : kemPtMsg m₁ m₂ (Fin.natAdd m₁ y) = none :=
  Fin.addCases_right y

/-- `kemPtMsg` is `some x` exactly at the left tagging of `x`. -/
theorem kemPtMsg_eq_some_iff (z : Fin (m₁ + m₂)) (x : Fin m₁) :
    kemPtMsg m₁ m₂ z = some x ↔ z = Fin.castAdd m₂ x := by
  induction z using Fin.addCases with
  | left x' =>
    rw [kemPtMsg_castAdd]
    exact ⟨fun h => by rw [Option.some_inj.mp h], fun h => by
      rw [Option.some_inj]
      exact (Fin.castAdd_injective m₁ m₂) h⟩
  | right y =>
    simp only [kemPtMsg_natAdd, reduceCtorEq, false_iff]
    intro hc
    have hval := congrArg Fin.val hc
    simp [Fin.natAdd, Fin.castAdd, Fin.castLE] at hval
    have := x.isLt
    omega

/-- The left tagging is determined by `kemPtMsg`. -/
theorem castAdd_injective_of_kemPtMsg (x x' : Fin m₁)
    (h : (Fin.castAdd m₂ x : Fin (m₁ + m₂)) = Fin.castAdd m₂ x') : x = x' := by
  have := congrArg (kemPtMsg m₁ m₂) h
  rw [kemPtMsg_castAdd, kemPtMsg_castAdd] at this
  exact Option.some_inj.mp this

end PointMap

section KemPoint

variable {m₁ m₂ n : ℕ} {PK SK M C K Hash Z : Type} (hpk : PK → Hash)
  (eG : (M × Hash) ≃ Fin m₁)

/-- The challenge point of the merged oracle: `kemPt hpk eG i` tagged into the
    left summand of `Fin (m₁ + m₂)`. -/
def kemPtMerged (i : KEMInput PK SK Z M K m₁ m₂ n) : Fin (m₁ + m₂) :=
  Fin.castAdd m₂ (kemPt hpk eG i)

/-- The punctured set of the challenge-key hop is the singleton at the tagged
    challenge point. -/
theorem mergeSet_kemPt_eq_singleton (i : KEMInput PK SK Z M K m₁ m₂ n) :
    mergeSet {kemPt hpk eG i} (∅ : Finset (Fin m₂)) = {kemPtMerged hpk eG i} := by
  simp [mergeSet, kemPtMerged]

/-- The point map reads the message-and-hash index off the tagged challenge
    point. -/
theorem kemPtMsg_kemPtMerged (i : KEMInput PK SK Z M K m₁ m₂ n) :
    kemPtMsg m₁ m₂ (kemPtMerged hpk eG i) = some (eG (i.2.2.1, hpk i.1.1)) :=
  kemPtMsg_castAdd _

/-- The challenge point determines the challenge message and the hashed public
    key. -/
theorem kemPt_inj (i i' : KEMInput PK SK Z M K m₁ m₂ n)
    (h : kemPt hpk eG i = kemPt hpk eG i') :
    (i.2.2.1, hpk i.1.1) = (i'.2.2.1, hpk i'.1.1) :=
  eG.injective h

/-- The tagged challenge point determines the challenge message and the hashed
    public key. -/
theorem kemPtMerged_inj (i i' : KEMInput PK SK Z M K m₁ m₂ n)
    (h : kemPtMerged hpk eG i = kemPtMerged hpk eG i') :
    (i.2.2.1, hpk i.1.1) = (i'.2.2.1, hpk i'.1.1) :=
  kemPt_inj hpk eG i i' (castAdd_injective_of_kemPtMsg _ _ h)

end KemPoint

/-! ## The traces of the two projectors -/

section Traces

/-- The trace of the query projector at a singleton is `n · W`. -/
theorem trace_projS_singleton (M n W : ℕ) (t : Fin M) :
    (projS M n W {t}).trace = (n : ℂ) * W := by
  unfold projS
  rw [trace_kronecker, trace_kronecker, Matrix.trace_diagonal, Matrix.trace_one, Matrix.trace_one]
  simp [indS]

/-- The trace of the output projector is `(m · n) · w`. -/
theorem trace_winProj (m n w : ℕ) (x : Fin m) :
    (winProj m n w x).trace = ((m : ℂ) * n) * w := by
  unfold winProj
  rw [trace_kronecker, trace_kronecker, Matrix.trace_diagonal, Matrix.trace_one, Matrix.trace_one]
  simp [indS]

end Traces

/-! ## The register obstruction -/

section Obstruction

/-- Equal total dimension and equal projector trace force the oracle domain of
    the adversary to be the message-index range of the `QOWAdv`. -/
theorem owcpa_register_forces_domain_eq {m₁ m₂ n W m w' : ℕ} (hn : 0 < n) (hw' : 0 < w')
    (hm : 0 < m) (hdim : (m₁ + m₂) * n * W = m * n * (m * w')) (hrank : n * W = m * n * w') :
    m₁ + m₂ = m := by
  have hW : W = m * w' := by
    refine Nat.eq_of_mul_eq_mul_left hn ?_
    rw [hrank]; ring
  subst hW
  refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hn (Nat.mul_pos hm hw')) ?_
  calc (m₁ + m₂) * (n * (m * w')) = (m₁ + m₂) * n * (m * w') := by ring
    _ = m * n * (m * w') := hdim
    _ = m * (n * (m * w')) := by ring

/-- A unitary carrying a projector of trace `n · W` to `winProj m n w' x` forces
    the oracle domain `m₁ + m₂` to equal the message-index range `m`, once the
    total dimensions agree. -/
theorem owcpa_embedding_obstruction {m₁ m₂ n W m w' : ℕ} (hn : 0 < n) (hw' : 0 < w')
    (hm : 0 < m) (hdim : (m₁ + m₂) * n * W = m * n * (m * w')) (x : Fin m)
    (proj : Matrix (Fin (m * n * (m * w'))) (Fin (m * n * (m * w'))) ℂ)
    (hproj : proj.trace = (n : ℂ) * W)
    (V : Matrix.unitaryGroup (Fin (m * n * (m * w'))) ℂ)
    (hV : winProj m n w' x = (V : Matrix _ _ ℂ) * proj * (V : Matrix _ _ ℂ)ᴴ) :
    m₁ + m₂ = m := by
  have htr : ((m : ℂ) * n) * w' = (n : ℂ) * W := by
    rw [← trace_winProj m n w' x, hV, trace_mul_mul_conjTranspose_of_mem_unitaryGroup V.prop,
      hproj]
  have hnat : m * n * w' = n * W := by
    have hc : ((m * n * w' : ℕ) : ℂ) = ((n * W : ℕ) : ℂ) := by push_cast; exact htr
    exact_mod_cast hc
  exact owcpa_register_forces_domain_eq hn hw' hm hdim hnat.symm

end Obstruction

/-! ## The index-range mismatch -/

section Mismatch

/-- The oracle domain of the KEM adversary equals the message-index range only
    when the hash type is a singleton and the second oracle summand is empty. -/
theorem kem_owcpa_index_mismatch {M Hash Z C : Type} [Fintype M] [Fintype Hash] [Fintype Z]
    [Fintype C] [Nonempty M] [Nonempty Hash] {m₁ m₂ m : ℕ} (eM : M ≃ Fin m)
    (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂) (h : m₁ + m₂ = m) :
    Fintype.card Hash = 1 ∧ Fintype.card Z * Fintype.card C = 0 := by
  have hm : m = Fintype.card M := ((Fintype.card_congr eM).trans (Fintype.card_fin m)).symm
  have hmJ : m₂ = Fintype.card Z * Fintype.card C := by
    rw [← Fintype.card_prod]
    exact ((Fintype.card_congr eJ).trans (Fintype.card_fin m₂)).symm
  have hm₁ : m₁ = Fintype.card M * Fintype.card Hash := by
    rw [← Fintype.card_prod]
    exact ((Fintype.card_congr eG).trans (Fintype.card_fin m₁)).symm
  have hM : 0 < Fintype.card M := Fintype.card_pos
  have hH : 1 ≤ Fintype.card Hash := Fintype.card_pos
  have hle : Fintype.card M * 1 ≤ m₁ := hm₁ ▸ Nat.mul_le_mul_left _ hH
  rw [Nat.mul_one] at hle
  have hm₂ : Fintype.card Z * Fintype.card C = 0 := by omega
  refine ⟨?_, hm₂⟩
  refine Nat.eq_of_mul_eq_mul_left hM ?_
  rw [Nat.mul_one]
  omega

end Mismatch

end CatCrypt.Quantum.QROM
