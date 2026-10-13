/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.KEMAdvNormalForm

/-!
# The normal form of a multi-round KEM adversary

Every multi-round adversary is simulated, on every observable `X ⊗ 1`, by an
adversary whose rounds all equal one fixed round: measure a record register in
the computational basis and answer by a shift of an answer register. Round `j`
of the original adversary becomes

* at the end of segment `j`, the copy `copyU` of its outcome into the record;
* the fixed round `slotRound`;
* at the start of segment `j + 1`, the answer unitaries controlled on the answer
  register, followed by the swap of the record and the answer register into
  the fresh slot `j` (`ansCtrlU`).

The state of the extended register stays classical on the extra register: a sum
`∑ t, σ t ⊗ |t⟩⟨t|` over the basis states `t` whose record, answer register and
slots `j, j + 1, …` are `0` (`SlotData.Good j`).

## Main definitions

* `SlotData E c a K` — the classical data of the extra register `Fin E`: the
  record and the answer register, their shifts, and the swaps into `K` slots
* `copyU`, `ansCtrlU`, `slotRound` — the three parts of a round in normal form
* `frontMul`, `backMul` — a unitary merged into the first or the last unitary of
  a segment
* `nfMR e S t₀ A` — the normal form of a multi-round adversary `A`
* `nfSlots`, `nfStart`, `nfAns` — the slot data on the ancilla of `permRound`,
  its zero state, and the answer family of `permRound`
* `nfKEM A` — the normal form of a KEM adversary

## Main results

* `trace_nfChain` — the multi-round chain of the normal form, on a classical
  extra register in a good state, agrees with the chain of `A` on every
  observable `X ⊗ 1` and every branch
* `prOutMR_nfMR` — the normal form outputs `1` with the probability of `A`
* `slotRound_eq_permRound`, `cleanProjM_eq_kr_nf` — in the `roundIndex` layout,
  the fixed round is `permRound` and the clean projector lives on the extra
  register
* `qINDCCAAdvantage_nfKEM`, `nfKEM_hseg`, `nfKEM_hrounds`, `nfKEM_hinit` — the
  normal form has the advantage of `A` and satisfies the four adversary-shape
  hypotheses `hw`, `hseg`, `hrounds`, `hinit` of `qINDCCA_le_find_numeric`

## Scope

The work register of `nfKEM A` is `w * (a * (c * a) ^ k * ancDim …)`: one answer
register and, for each of the `k` rounds, a slot holding the record and the
answer of that round. The answer alphabet is nonempty (`NeZero a`), which the KEM
game implies through `eKa : K ≃ Fin a` and `Nonempty K`.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
  CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Basis matrices of a classical register -/

section Basis

variable {E : ℕ}

/-- The diagonal indicator of a predicate on `Fin E`. -/
def indE (p : Fin E → Prop) [DecidablePred p] : Matrix (Fin E) (Fin E) ℂ :=
  Matrix.diagonal fun t => if p t then 1 else 0

theorem permUnitary_mul_ancUnit (π : Equiv.Perm (Fin E)) (u u' : Fin E) :
    (permUnitary π : Matrix (Fin E) (Fin E) ℂ) * ancUnit u u' = ancUnit (π u) u' := by
  ext i j
  simp only [Matrix.mul_apply, permUnitary_apply, ancUnit, Matrix.of_apply]
  rw [Finset.sum_eq_single u]
  · by_cases hi : i = π u <;> by_cases hj : j = u' <;> simp [hi, hj]
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ u) h

theorem ancUnit_mul_permUnitary_conjTranspose (π : Equiv.Perm (Fin E)) (u u' : Fin E) :
    ancUnit u u' * (permUnitary π : Matrix (Fin E) (Fin E) ℂ)ᴴ = ancUnit u (π u') := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, permUnitary_apply, ancUnit,
    Matrix.of_apply]
  rw [Finset.sum_eq_single u']
  · by_cases hi : i = u <;> by_cases hj : j = π u' <;> simp [hi, hj]
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ u') h

theorem permUnitary_conj_ancUnit (π : Equiv.Perm (Fin E)) (u u' : Fin E) :
    (permUnitary π : Matrix (Fin E) (Fin E) ℂ) * ancUnit u u' *
        (permUnitary π : Matrix (Fin E) (Fin E) ℂ)ᴴ = ancUnit (π u) (π u') := by
  rw [permUnitary_mul_ancUnit, ancUnit_mul_permUnitary_conjTranspose]

theorem indE_mul_ancUnit (p : Fin E → Prop) [DecidablePred p] (u u' : Fin E) :
    indE p * ancUnit u u' = if p u then ancUnit u u' else 0 := by
  ext i j
  by_cases hp : p u
  · rw [if_pos hp]
    simp only [indE, Matrix.diagonal_mul, ancUnit, Matrix.of_apply]
    by_cases hi : i = u
    · subst hi; simp [hp]
    · simp [hi]
  · rw [if_neg hp]
    simp only [indE, Matrix.diagonal_mul, ancUnit, Matrix.of_apply, Matrix.zero_apply]
    by_cases hi : i = u
    · subst hi; simp [hp]
    · simp [hi]

theorem ancUnit_mul_indE (p : Fin E → Prop) [DecidablePred p] (u u' : Fin E) :
    ancUnit u u' * indE p = if p u' then ancUnit u u' else 0 := by
  ext i j
  by_cases hp : p u'
  · rw [if_pos hp]
    simp only [indE, Matrix.mul_diagonal, ancUnit, Matrix.of_apply]
    by_cases hj : j = u'
    · subst hj; simp [hp]
    · simp [hj]
  · rw [if_neg hp]
    simp only [indE, Matrix.mul_diagonal, ancUnit, Matrix.of_apply, Matrix.zero_apply]
    by_cases hj : j = u'
    · subst hj; simp [hp]
    · simp [hj]

theorem indE_conjTranspose (p : Fin E → Prop) [DecidablePred p] : (indE p)ᴴ = indE p := by
  rw [indE, Matrix.diagonal_conjTranspose]
  congr 1
  funext t
  by_cases h : p t <;> simp [h]

theorem indE_mul_indE_eq {ι : Type} [DecidableEq ι] (g : Fin E → ι) (y y' : ι) :
    (indE fun t => g t = y) * (indE fun t => g t = y') =
      if y = y' then indE fun t => g t = y else 0 := by
  simp only [indE, Matrix.diagonal_mul_diagonal]
  split_ifs with h
  · subst h
    congr 1
    funext t
    by_cases ht : g t = y <;> simp [ht]
  · rw [← Matrix.diagonal_zero]
    congr 1
    funext t
    by_cases ht : g t = y
    · simp [ht, h]
    · simp [ht]

theorem sum_indE_eq {ι : Type} [Fintype ι] [DecidableEq ι] (g : Fin E → ι) :
    ∑ y, (indE fun t => g t = y) = (1 : Matrix (Fin E) (Fin E) ℂ) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [indE, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- `permUnitary π` commutes with the indicator of a predicate that `π`
preserves. -/
theorem permUnitary_mul_indE_comm (π : Equiv.Perm (Fin E)) (p : Fin E → Prop)
    [DecidablePred p] (hp : ∀ t, p (π t) ↔ p t) :
    (permUnitary π : Matrix (Fin E) (Fin E) ℂ) * indE p =
      indE p * (permUnitary π : Matrix (Fin E) (Fin E) ℂ) := by
  ext i j
  simp only [indE, Matrix.mul_diagonal, Matrix.diagonal_mul, permUnitary_apply]
  by_cases h : i = π j
  · subst h
    simp only [if_true, hp j, one_mul, mul_one]
  · simp [h]

theorem indE_mul_indE_comm (p p' : Fin E → Prop) [DecidablePred p] [DecidablePred p'] :
    indE p * indE p' = indE p' * indE p := by
  rw [indE, indE, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext t
  ring

end Basis

/-! ## The classical extra register and the three parts of a round -/

/-- The classical data of an extra register `Fin E` for rounds with outcomes
`Fin c`, answers `Fin a` and `K` fresh slots: the record and the answer
register read off a basis state, their shifts, the swap of both into slot `j`,
and the basis states `Good j` whose record, answer register and slots
`j, j + 1, …` are `0`. -/
structure SlotData (E c a K : ℕ) where
  /-- The record of a basis state. -/
  recv : Fin E → Fin c
  /-- The answer register of a basis state. -/
  ansv : Fin E → Fin a
  /-- The shift of the record by an outcome. -/
  recShift : Fin c → Equiv.Perm (Fin E)
  /-- The shift of the answer register by an answer. -/
  ansShift : Fin a → Equiv.Perm (Fin E)
  /-- The swap of the record and the answer register into slot `j`. -/
  swap : ℕ → Equiv.Perm (Fin E)
  /-- The basis states with record, answer register and slots from `j` on at `0`. -/
  Good : ℕ → Fin E → Prop
  recv_recShift : ∀ j t, Good j t → ∀ y, recv (recShift y t) = y
  ansv_ansShift : ∀ j t, Good j t → ∀ y z, ansv (ansShift z (recShift y t)) = z
  good_swap : ∀ j t, j < K → Good j t → ∀ y z, Good (j + 1) (swap j (ansShift z (recShift y t)))

section Round

variable {d E D c a K : ℕ}

/-- The permutation unitary of `π` on the extra register, `1 ⊗ π`. -/
def liftE (e : Fin (d * E) ≃ Fin D) (π : Equiv.Perm (Fin E)) : Matrix.unitaryGroup (Fin D) ℂ :=
  ⟨kr e 1 (permUnitary π), kr_mem_unitaryGroup e (one_mem _) (permUnitary π).prop⟩

theorem liftE_val (e : Fin (d * E) ≃ Fin D) (π : Equiv.Perm (Fin E)) :
    (liftE e π : Matrix (Fin D) (Fin D) ℂ) = kr e 1 (permUnitary π) := rfl

theorem permUnitary_mul_conjTranspose_self (π : Equiv.Perm (Fin E)) :
    (permUnitary π : Matrix (Fin E) (Fin E) ℂ) * (permUnitary π : Matrix (Fin E) (Fin E) ℂ)ᴴ =
      1 := by
  rw [← star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff.mp (permUnitary π).prop

/-- The copy of the outcome of `R` into the record: `∑ y, P y ⊗ recShift y`. -/
def copyU (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K) (R : ClassicalRound d c a) :
    Matrix.unitaryGroup (Fin D) ℂ :=
  ⟨∑ y, kr e (R.P y) (permUnitary (S.recShift y)), by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_sum,
      Finset.sum_mul_sum]
    simp only [kr_conjTranspose, kr_mul, R.P_conjTranspose]
    have h : ∀ y, ∑ y', kr e (R.P y * R.P y') ((permUnitary (S.recShift y) :
        Matrix (Fin E) (Fin E) ℂ) * (permUnitary (S.recShift y') : Matrix (Fin E) (Fin E) ℂ)ᴴ) =
        kr e (R.P y) 1 := by
      intro y
      rw [Finset.sum_eq_single y]
      · rw [R.P_mul_self, permUnitary_mul_conjTranspose_self]
      · intro y' _ hy'; rw [R.P_orth y y' (Ne.symm hy'), kr_zero_left]
      · intro h; exact absurd (Finset.mem_univ y) h
    simp only [h, ← kr_sum_left, R.P_sum, kr_one]⟩

theorem copyU_val (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K) (R : ClassicalRound d c a) :
    (copyU e S R : Matrix (Fin D) (Fin D) ℂ) = ∑ y, kr e (R.P y) (permUnitary (S.recShift y)) :=
  rfl

/-- The answer unitaries of `R` controlled on the answer register. -/
def ctrlE (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K) (R : ClassicalRound d c a) :
    Matrix (Fin D) (Fin D) ℂ :=
  ∑ z, kr e (R.ans z : Matrix (Fin d) (Fin d) ℂ) (indE fun t => S.ansv t = z)

theorem ctrlE_mem (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K) (R : ClassicalRound d c a) :
    ctrlE e S R ∈ Matrix.unitaryGroup (Fin D) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, ctrlE, conjTranspose_sum,
    Finset.sum_mul_sum]
  simp only [kr_conjTranspose, kr_mul, indE_conjTranspose, indE_mul_indE_eq]
  have h : ∀ z, ∑ z', kr e ((R.ans z : Matrix (Fin d) (Fin d) ℂ) *
      (R.ans z' : Matrix (Fin d) (Fin d) ℂ)ᴴ)
        (if z = z' then indE fun t => S.ansv t = z else 0) =
      kr e 1 (indE fun t => S.ansv t = z) := by
    intro z
    rw [Finset.sum_eq_single z]
    · rw [if_pos rfl, ← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp (R.ans z).prop]
    · intro z' _ hz'; rw [if_neg (Ne.symm hz'), kr_zero_right]
    · intro h; exact absurd (Finset.mem_univ z) h
  simp only [h, ← kr_sum_right, sum_indE_eq, kr_one]

/-- The answer of `R` controlled on the answer register, followed by the swap
of the record and the answer register into slot `j`. -/
def ansCtrlU (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K) (j : ℕ)
    (R : ClassicalRound d c a) : Matrix.unitaryGroup (Fin D) ℂ :=
  liftE e (S.swap j) * ⟨ctrlE e S R, ctrlE_mem e S R⟩

theorem ansCtrlU_val (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K) (j : ℕ)
    (R : ClassicalRound d c a) :
    (ansCtrlU e S j R : Matrix (Fin D) (Fin D) ℂ) = kr e 1 (permUnitary (S.swap j)) * ctrlE e S R :=
  rfl

/-- The round measuring the record in the computational basis and answering `z`
by the shift of the answer register. -/
def slotRound (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K) : ClassicalRound D c a where
  P y := kr e 1 (indE fun t => S.recv t = y)
  P_conjTranspose y := by rw [kr_conjTranspose, conjTranspose_one, indE_conjTranspose]
  P_mul_self y := by rw [kr_mul, one_mul, indE_mul_indE_eq, if_pos rfl]
  P_orth y y' h := by rw [kr_mul, indE_mul_indE_eq, if_neg h, kr_zero_right]
  P_sum := by rw [← kr_sum_right, sum_indE_eq, kr_one]
  ans z := liftE e (S.ansShift z)

/-! ### The three parts on a basis state of the extra register -/

theorem copyU_conj (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K) (R : ClassicalRound d c a)
    (σ : Matrix (Fin d) (Fin d) ℂ) (t : Fin E) :
    (copyU e S R : Matrix (Fin D) (Fin D) ℂ) * kr e σ (ancUnit t t) *
        (copyU e S R : Matrix (Fin D) (Fin D) ℂ)ᴴ =
      ∑ y, ∑ y', kr e (R.P y * σ * R.P y') (ancUnit (S.recShift y t) (S.recShift y' t)) := by
  rw [copyU_val, conjTranspose_sum, Finset.sum_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
  rw [kr_mul, kr_conjTranspose, kr_mul, R.P_conjTranspose, permUnitary_mul_ancUnit,
    ancUnit_mul_permUnitary_conjTranspose]

theorem conj_perm_indE_ancUnit (π : Equiv.Perm (Fin E)) (p : Fin E → Prop) [DecidablePred p]
    (u u' : Fin E) :
    (permUnitary π : Matrix (Fin E) (Fin E) ℂ) * indE p * ancUnit u u' *
        ((permUnitary π : Matrix (Fin E) (Fin E) ℂ) * indE p)ᴴ =
      if p u ∧ p u' then ancUnit (π u) (π u') else 0 := by
  rw [conjTranspose_mul, indE_conjTranspose, Matrix.mul_assoc _ (indE p), indE_mul_ancUnit]
  by_cases hu : p u
  · rw [if_pos hu, ← Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (ancUnit u u'), ancUnit_mul_indE]
    by_cases hu' : p u'
    · rw [if_pos hu', if_pos ⟨hu, hu'⟩, ← Matrix.mul_assoc, permUnitary_conj_ancUnit]
    · rw [if_neg hu', if_neg fun h => hu' h.2, zero_mul, mul_zero]
  · rw [if_neg hu, if_neg fun h => hu h.1, mul_zero, zero_mul]

theorem roundU_slotRound_branch (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K)
    (f : Fin c → Fin a) (B : Fin c → Fin c → Matrix (Fin d) (Fin d) ℂ) (u : Fin c → Fin E)
    (hu : ∀ y, S.recv (u y) = y) :
    (roundU (slotRound e S) f).branch () (∑ y, ∑ y', kr e (B y y') (ancUnit (u y) (u y'))) =
      ∑ y, kr e (B y y) (ancUnit (S.ansShift (f y) (u y)) (S.ansShift (f y) (u y))) := by
  rw [roundU_branch]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hop : ((slotRound e S).ans (f z) : Matrix (Fin D) (Fin D) ℂ) * (slotRound e S).P z =
      kr e 1 ((permUnitary (S.ansShift (f z)) : Matrix (Fin E) (Fin E) ℂ) *
        indE fun t => S.recv t = z) := by
    show kr e 1 _ * kr e 1 _ = _
    rw [kr_mul, one_mul]
  rw [hop, Finset.mul_sum, Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_mul, kr_conjTranspose, kr_mul, one_mul,
    conjTranspose_one, mul_one, conj_perm_indE_ancUnit, hu]
  rw [Finset.sum_eq_single z, Finset.sum_eq_single z]
  · rw [if_pos ⟨rfl, rfl⟩]
  · intro y' _ hy'; rw [if_neg fun h => hy' h.2, kr_zero_right]
  · intro h; exact absurd (Finset.mem_univ z) h
  · intro y _ hy
    exact Finset.sum_eq_zero fun y' _ => by rw [if_neg fun h => hy h.1, kr_zero_right]
  · intro h; exact absurd (Finset.mem_univ z) h

theorem ctrlE_mul_kr_ancUnit (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K)
    (R : ClassicalRound d c a) (B : Matrix (Fin d) (Fin d) ℂ) (v : Fin E) :
    ctrlE e S R * kr e B (ancUnit v v) * (ctrlE e S R)ᴴ =
      kr e ((R.ans (S.ansv v) : Matrix (Fin d) (Fin d) ℂ) * B *
        (R.ans (S.ansv v) : Matrix (Fin d) (Fin d) ℂ)ᴴ) (ancUnit v v) := by
  rw [ctrlE, conjTranspose_sum, Finset.sum_mul, Finset.sum_mul_sum]
  simp only [kr_conjTranspose, kr_mul, indE_conjTranspose, indE_mul_ancUnit, ite_mul, zero_mul,
    ancUnit_mul_indE]
  rw [Finset.sum_eq_single (S.ansv v), Finset.sum_eq_single (S.ansv v)]
  · simp
  · intro z' _ hz'; simp [Ne.symm hz', kr_zero_right]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro z _ hz
    exact Finset.sum_eq_zero fun z' _ => by simp [Ne.symm hz, kr_zero_right]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem ansCtrlU_conj (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K) (j : ℕ)
    (R : ClassicalRound d c a) (B : Matrix (Fin d) (Fin d) ℂ) (v : Fin E) :
    (ansCtrlU e S j R : Matrix (Fin D) (Fin D) ℂ) * kr e B (ancUnit v v) *
        (ansCtrlU e S j R : Matrix (Fin D) (Fin D) ℂ)ᴴ =
      kr e ((R.ans (S.ansv v) : Matrix (Fin d) (Fin d) ℂ) * B *
        (R.ans (S.ansv v) : Matrix (Fin d) (Fin d) ℂ)ᴴ) (ancUnit (S.swap j v) (S.swap j v)) := by
  rw [ansCtrlU_val, conjTranspose_mul]
  have h : kr e 1 (permUnitary (S.swap j) : Matrix (Fin E) (Fin E) ℂ) * ctrlE e S R *
      kr e B (ancUnit v v) * ((ctrlE e S R)ᴴ *
        (kr e 1 (permUnitary (S.swap j) : Matrix (Fin E) (Fin E) ℂ))ᴴ) =
      kr e 1 (permUnitary (S.swap j) : Matrix (Fin E) (Fin E) ℂ) *
        (ctrlE e S R * kr e B (ancUnit v v) * (ctrlE e S R)ᴴ) *
        (kr e 1 (permUnitary (S.swap j) : Matrix (Fin E) (Fin E) ℂ))ᴴ := by
    simp only [Matrix.mul_assoc]
  rw [h, ctrlE_mul_kr_ancUnit, kr_conjTranspose, kr_mul, kr_mul, one_mul, conjTranspose_one,
    mul_one, permUnitary_conj_ancUnit]

/-- **One round in normal form on a good basis state.** The copy, the fixed
round and the controlled answer with the swap into slot `j` take `σ ⊗ |t⟩⟨t|`
to the sum over the outcomes `y` of the outcome-`y` branch of `R` next to the
basis state recording `y` and `f y` in slot `j`. -/
theorem block_conj (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K) (j j' : ℕ)
    (R : ClassicalRound d c a) (f : Fin c → Fin a) (σ : Matrix (Fin d) (Fin d) ℂ) (t : Fin E)
    (ht : S.Good j' t) :
    (ansCtrlU e S j R : Matrix (Fin D) (Fin D) ℂ) * (roundU (slotRound e S) f).branch ()
        ((copyU e S R : Matrix (Fin D) (Fin D) ℂ) * kr e σ (ancUnit t t) *
          (copyU e S R : Matrix (Fin D) (Fin D) ℂ)ᴴ) *
        (ansCtrlU e S j R : Matrix (Fin D) (Fin D) ℂ)ᴴ =
      ∑ y, kr e (((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y) * σ *
          ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y)ᴴ)
        (ancUnit (S.swap j (S.ansShift (f y) (S.recShift y t)))
          (S.swap j (S.ansShift (f y) (S.recShift y t)))) := by
  rw [copyU_conj, roundU_slotRound_branch e S f _ _ (S.recv_recShift j' t ht), Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ansCtrlU_conj, S.ansv_ansShift j' t ht, conjTranspose_mul, R.P_conjTranspose]
  simp only [Matrix.mul_assoc]

end Round

/-! ## Unitaries merged into the ends of a segment -/

section Merge

variable {d : ℕ}

/-- The segment `U` with `W` applied before its first unitary. -/
def frontMul {q : ℕ} (W : Matrix.unitaryGroup (Fin d) ℂ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ :=
  Fin.cons (U 0 * W) (Fin.tail U)

/-- The segment `U` with `V` applied after its last unitary. -/
def backMul (V : Matrix.unitaryGroup (Fin d) ℂ) :
    (q : ℕ) → (Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ
  | 0, U => fun _ => V * U 0
  | q + 1, U => Fin.cons (U 0) (backMul V q (Fin.tail U))

theorem scChain_frontMul (O : QComp d Bool) (W : Matrix.unitaryGroup (Fin d) ℂ) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    scChain O q (frontMul W U) = QComp.qbind (unitaryChannel W) fun _ => scChain O q U := by
  cases q <;>
    simp only [scChain, frontMul, Fin.cons_zero, Fin.tail_cons, ← unitaryChannel_compose,
      QComp.qbind_assoc]

theorem scChain_backMul (O : QComp d Bool) (V : Matrix.unitaryGroup (Fin d) ℂ) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      scChain O q (backMul V q U) = QComp.qbind (scChain O q U) fun b =>
        QComp.qbind (unitaryChannel V) fun _ => QComp.qpure b
  | 0, U => by
    simp only [scChain, backMul, ← unitaryChannel_compose, QComp.qbind_assoc, QComp.qpure_qbind]
  | q + 1, U => by
    simp only [scChain, backMul, Fin.cons_zero, Fin.tail_cons, scChain_backMul O V q,
      QComp.qbind_assoc, QComp.qpure_qbind]

theorem scChain_backMul_branch (O : QComp d Bool) (V : Matrix.unitaryGroup (Fin d) ℂ) (q : ℕ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (b : Bool) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (scChain O q (backMul V q U)).branch b ρ =
      (V : Matrix (Fin d) (Fin d) ℂ) * (scChain O q U).branch b ρ * (V : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
  rw [scChain_backMul, qbind_bool_branch, qbind_unit_branch, qbind_unit_branch,
    qpure_branch_apply, qpure_branch_apply, unitaryChannel_branch_apply,
    unitaryChannel_branch_apply]
  cases b <;> simp

variable {c a : ℕ}

theorem mrChainSC_frontMul_branch {q : ℕ} (O : QComp d Bool) (f : Fin c → Fin a) (k q₀ : ℕ)
    (W : Matrix.unitaryGroup (Fin d) ℂ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin k → ClassicalRound d c a) (b : Bool) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (mrChainSC O f k q₀ (frontMul W head) tail R).branch b ρ =
      (mrChainSC O f k q₀ head tail R).branch b
        ((W : Matrix (Fin d) (Fin d) ℂ) * ρ * (W : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
  have h : mrChainSC O f k q₀ (frontMul W head) tail R =
      QComp.qbind (unitaryChannel W) fun _ => mrChainSC O f k q₀ head tail R := by
    cases k <;> simp only [mrChainSC, scChain_frontMul, QComp.qbind_assoc]
  rw [h, qbind_unit_branch, unitaryChannel_branch_apply]

end Merge

/-! ## The multi-round chain in normal form -/

section Chain

variable {d E D c a K q : ℕ}

/-- **The multi-round chain in normal form.** Segment `0` carries the copy of
round `0` at its end; segment `j + 1` carries the controlled answer of round `j`
with the swap into slot `j₀ + j` at its start and the copy of round `j + 1` at
its end; every round is `slotRound`. On `σ ⊗ |t⟩⟨t|` with `t` good from `j₀`, the
chain agrees with the multi-round chain of the rounds `R` on `σ` on every
observable `X ⊗ 1` and every branch. -/
theorem trace_nfChain (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K) (O : QComp d Bool)
    (O' : QComp D Bool) (hO : LiftsQ e O O') (f : Fin c → Fin a) :
    ∀ (k j₀ q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (Vs : Fin (k + 1) → Matrix.unitaryGroup (Fin D) ℂ)
      (Ws : Fin k → Matrix.unitaryGroup (Fin D) ℂ), j₀ + k ≤ K →
      (∀ j : Fin k, Vs j.castSucc = copyU e S (R j)) → Vs (Fin.last k) = 1 →
      (∀ j : Fin k, Ws j = ansCtrlU e S (j₀ + j) (R j)) →
      ∀ t, S.Good j₀ t → ∀ (X σ : Matrix (Fin d) (Fin d) ℂ) (b : Bool),
      (kr e X 1 * (mrChainSC O' f k q₀ (backMul (Vs 0) q₀ (liftU e ∘ head))
          (fun j => frontMul (Ws j) (backMul (Vs j.succ) q (liftU e ∘ tail j)))
          (fun _ => slotRound e S)).branch b (kr e σ (ancUnit t t))).trace =
        (X * (mrChainSC O f k q₀ head tail R).branch b σ).trace
  | 0, j₀, q₀, head, tail, R, Vs, Ws, _, _, hlast, _, t, _, X, σ, b => by
    have h0 : Vs 0 = 1 := hlast
    show (kr e X 1 * (scChain O' q₀ (backMul (Vs 0) q₀ (liftU e ∘ head))).branch b
      (kr e σ (ancUnit t t))).trace = (X * (scChain O q₀ head).branch b σ).trace
    rw [scChain_backMul_branch, h0, liftsQ_scChain e O O' hO q₀ head b σ (ancUnit t t)]
    simp only [OneMemClass.coe_one, one_mul, conjTranspose_one, mul_one]
    rw [kr_mul, one_mul, trace_kr, trace_ancUnit, if_pos rfl, mul_one]
  | k + 1, j₀, q₀, head, tail, R, Vs, Ws, hk, hV, hlast, hW, t, ht, X, σ, b => by
    rw [mrChainSC_succ_branch, mrChainSC_succ_branch]
    simp_rw [Finset.mul_sum, trace_sum]
    refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
    split_ifs
    · have hV0 : Vs 0 = copyU e S (R 0) := hV 0
      have hW0 : Ws 0 = ansCtrlU e S j₀ (R 0) := hW 0
      rw [scChain_backMul_branch, liftsQ_scChain e O O' hO q₀ head b₁ σ (ancUnit t t), hV0]
      show (kr e X 1 * (mrChainSC O' f k q (frontMul (Ws 0) (backMul (Vs 1) q (liftU e ∘ tail 0)))
        (fun j => frontMul (Ws j.succ) (backMul (Vs j.succ.succ) q (liftU e ∘ Fin.tail tail j)))
        (fun _ => slotRound e S)).branch b₂ _).trace = _
      rw [mrChainSC_frontMul_branch, hW0, block_conj e S j₀ j₀ (R 0) f _ t ht, map_sum,
        Finset.mul_sum, trace_sum, roundU_branch, map_sum, Finset.mul_sum, trace_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      exact trace_nfChain e S O O' hO f k (j₀ + 1) q (tail 0) (Fin.tail tail) (Fin.tail R)
        (fun j => Vs j.succ) (fun j => Ws j.succ) (by omega)
        (fun j => by rw [Fin.succ_castSucc]; exact hV j.succ)
        (by rw [Fin.succ_last]; exact hlast)
        (fun j => by
          rw [hW j.succ, Fin.val_succ]
          congr 1
          omega)
        _ (S.good_swap j₀ t (by omega) ht y (f y)) X _ b₂
    · simp

end Chain

/-! ## The normal form of a multi-round adversary -/

section NF

variable {m n W E W' q k c a : ℕ}

/-- The unitaries at the ends of the segments: the copy of round `j` at the end
of segment `j`, and `1` at the end of the last segment. -/
def nfV {d D : ℕ} (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a k)
    (R : Fin k → ClassicalRound d c a) : Fin (k + 1) → Matrix.unitaryGroup (Fin D) ℂ :=
  Fin.lastCases 1 fun j => copyU e S (R j)

/-- The unitaries at the starts of the segments: `1` at the start of segment
`0`, and the controlled answer of round `j` with the swap into slot `j` at the
start of segment `j + 1`. -/
def nfW {d D : ℕ} (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a k)
    (R : Fin k → ClassicalRound d c a) : Fin (k + 1) → Matrix.unitaryGroup (Fin D) ℂ :=
  Fin.cases 1 fun j => ansCtrlU e S j (R j)

/-- The normal form of `A` on the register extended by `Fin E` along `e`: the
segments of `A` tensored with `1`, with the copies and the controlled answers
merged into their ends, every round `slotRound e S`, the initial state
`ρ ⊗ |t₀⟩⟨t₀|` and the final projector `P ⊗ 1`. -/
def nfMR (e : Fin (m * n * W * E) ≃ Fin (m * n * W')) (S : SlotData E c a k) (t₀ : Fin E)
    (A : QAdvMR m n W q k c a) : QAdvMR m n W' q k c a where
  seg j := frontMul (nfW e S A.rounds j) (backMul (nfV e S A.rounds j) q (liftU e ∘ A.seg j))
  rounds _ := slotRound e S
  init :=
    { val := kr e A.init.val (ancProj t₀)
      psd := kr_posSemidef _ A.init.psd (ancProj_posSemidef t₀)
      tr_one := by rw [trace_kr, A.init.tr_one, trace_ancProj, one_mul] }
  final := kr e A.final 1
  final_conjTranspose := by rw [kr_conjTranspose, A.final_conjTranspose, conjTranspose_one]
  final_mul_self := by rw [kr_mul, A.final_mul_self, one_mul]

/-- **The normal form outputs `1` with the probability of `A`**, for an initial
basis state `t₀` good from slot `0`. -/
theorem prOutMR_nfMR [NeZero n] (hW : W * E = W') (S : SlotData E c a k) (t₀ : Fin E)
    (ht₀ : S.Good 0 t₀) (A : QAdvMR m n W q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    prOutMR (nfMR (padE m n hW) S t₀ A) H f = prOutMR A H f := by
  subst hW
  rw [prOutMR_eq_trace, prOutMR_eq_trace]
  refine congrArg (fun t : ℂ => ENNReal.ofReal t.re) ?_
  show (kr (ancE m n W E) A.final 1 * (mrChainSC (scOracleQ m n (W * E) H ∅) f k q
      (frontMul 1 (backMul (nfV (ancE m n W E) S A.rounds 0) q (liftU (ancE m n W E) ∘ A.seg 0)))
      (fun j => frontMul (nfW (ancE m n W E) S A.rounds j.succ)
        (backMul (nfV (ancE m n W E) S A.rounds j.succ) q
          (liftU (ancE m n W E) ∘ Fin.tail A.seg j)))
      (fun _ => slotRound (ancE m n W E) S)).branch false
        (kr (ancE m n W E) A.init.val (ancProj t₀))).trace = _
  rw [mrChainSC_frontMul_branch]
  simp only [OneMemClass.coe_one, one_mul, conjTranspose_one, mul_one, ← ancUnit_self]
  exact trace_nfChain (ancE m n W E) S _ _ (liftsQ_scOracleQ H ∅) f k 0 q (A.seg 0)
    (Fin.tail A.seg) A.rounds _ _ (by omega)
    (fun j => by simp [nfV]) (by simp [nfV]) (fun j => by simp [nfW]) t₀ ht₀ A.final
    A.init.val false

theorem castMR_nfMR {W₂ : ℕ} (hW : W * E = W') (h : W' = W₂) (S : SlotData E c a k)
    (t₀ : Fin E) (A : QAdvMR m n W q k c a) :
    castMR h (nfMR (padE m n hW) S t₀ A) = nfMR (padE m n (hW.trans h)) S t₀ A := by
  subst h
  rfl

end NF

/-! ## The slot register on the ancilla of `permRound` -/

section Slots

variable (M n c a k : ℕ) [NeZero M] [NeZero n] [NeZero c] [NeZero a]

/-- The number of basis states of the answer register and the `k` slots. -/
def nfX : ℕ := a * (c * a) ^ k

/-- The answer register and the `k` slots, each holding a record and an answer. -/
abbrev SlotReg : Type := Fin a × (Fin k → Fin c × Fin a)

/-- The row-major index of the slot register. -/
def slotIndex : SlotReg c a k ≃ Fin (nfX c a k) :=
  ((Equiv.refl (Fin a)).prodCongr ((Equiv.arrowCongr (Equiv.refl (Fin k))
    (finProdEquiv c a)).trans finFunctionFinEquiv)).trans (finProdEquiv a ((c * a) ^ k))

/-- The extra register: the slot register and the ancilla of `permRound`. -/
abbrev ExtReg : Type := SlotReg c a k × RoundAnc M n c

/-- The row-major index of the extra register. -/
def extIndex : ExtReg M n c a k ≃ Fin (nfX c a k * ancDim M n c) :=
  ((slotIndex c a k).prodCongr (ancIndex M n c)).trans (finProdEquiv _ _)

/-- The swap of the record and the answer register with slot `i`. -/
def swapFun (i : Fin k) (s : ExtReg M n c a k) : ExtReg M n c a k :=
  (((s.1.2 i).2, Function.update s.1.2 i (s.2.1, s.1.1)), ((s.1.2 i).1, s.2.2))

omit [NeZero M] [NeZero n] [NeZero c] [NeZero a] in
theorem swapFun_involutive (i : Fin k) : Function.Involutive (swapFun M n c a k i) := by
  rintro ⟨⟨an, sl⟩, r, p⟩
  simp [swapFun]

/-- The swap of the record and the answer register into slot `j`, the identity
for `j ≥ k`. -/
def swapR (j : ℕ) : Equiv.Perm (ExtReg M n c a k) :=
  if h : j < k then (swapFun_involutive M n c a k ⟨j, h⟩).toPerm _ else 1

/-- The slot data of the extra register: the record is the record slot of the
ancilla, the answer register is the first factor of the slot register. -/
def nfSlots : SlotData (nfX c a k * ancDim M n c) c a k where
  recv t := ((extIndex M n c a k).symm t).2.1
  ansv t := ((extIndex M n c a k).symm t).1.1
  recShift y := (extIndex M n c a k).permCongr
    ((Equiv.refl _).prodCongr ((Equiv.addRight y).prodCongr (Equiv.refl _)))
  ansShift z := (extIndex M n c a k).permCongr
    (((Equiv.addRight z).prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _))
  swap j := (extIndex M n c a k).permCongr (swapR M n c a k j)
  Good j t := ((extIndex M n c a k).symm t).2.1 = 0 ∧ ((extIndex M n c a k).symm t).1.1 = 0 ∧
    ∀ i : Fin k, j ≤ i → ((extIndex M n c a k).symm t).1.2 i = (0, 0)
  recv_recShift j t ht y := by
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply,
      Prod.map, Equiv.coe_refl, id, Equiv.coe_addRight, ht.1, zero_add]
  ansv_ansShift j t ht y z := by
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply,
      Prod.map, Equiv.coe_refl, id, Equiv.coe_addRight, ht.2.1, zero_add]
  good_swap j t hj ht y z := by
    obtain ⟨⟨⟨an, sl⟩, r, p⟩, rfl⟩ := (extIndex M n c a k).surjective t
    simp only [Equiv.symm_apply_apply] at ht
    obtain ⟨hr, han, hsl⟩ := ht
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply,
      Prod.map, Equiv.coe_refl, id, Equiv.coe_addRight, swapR, dif_pos hj,
      Function.Involutive.coe_toPerm, swapFun]
    refine ⟨(congrArg Prod.fst (hsl ⟨j, hj⟩ le_rfl)), (congrArg Prod.snd (hsl ⟨j, hj⟩ le_rfl)),
      fun i hi => ?_⟩
    have hne : i ≠ ⟨j, hj⟩ := fun h => by rw [h] at hi; exact absurd hi (by simp)
    rw [Function.update_of_ne hne]
    exact hsl i (by omega)

/-- The basis state with every slot, the record, the answer register and the
parked slots at `0`. -/
def nfStart : Fin (nfX c a k * ancDim M n c) :=
  extIndex M n c a k ((0, fun _ => (0, 0)), (0, (0, 0), (0, 0)))

theorem nfStart_good : (nfSlots M n c a k).Good 0 (nfStart M n c a k) := by
  simp [nfSlots, nfStart]

/-- The basis states whose parked slots are `0`. -/
def nfClean (t : Fin (nfX c a k * ancDim M n c)) : Prop :=
  ((extIndex M n c a k).symm t).2.2 = ((0, 0), (0, 0))

instance (t : Fin (nfX c a k * ancDim M n c)) : Decidable (nfClean M n c a k t) := by
  unfold nfClean; infer_instance

end Slots

/-! ## Matrices on the extra register in the `roundIndex` layout -/

section KrForm

variable {d E D : ℕ}

theorem kr_one_apply (e : Fin (d * E) ≃ Fin D) (B : Matrix (Fin E) (Fin E) ℂ) (u u' : Fin d)
    (t t' : Fin E) :
    kr e 1 B (e (finProdEquiv d E (u, t))) (e (finProdEquiv d E (u', t'))) =
      if u = u' then B t t' else 0 := by
  simp only [kr, Matrix.submatrix_apply, Equiv.symm_apply_apply, kronecker_apply,
    Matrix.one_apply]
  split_ifs <;> simp

/-- A diagonal matrix constant along the first factor is `1 ⊗ diagonal`. -/
theorem diagonal_eq_kr_one (e : Fin (d * E) ≃ Fin D) (g : Fin D → ℂ) (h : Fin E → ℂ)
    (hg : ∀ u t, g (e (finProdEquiv d E (u, t))) = h t) :
    Matrix.diagonal g = kr e 1 (Matrix.diagonal h) := by
  ext i j
  obtain ⟨⟨u, t⟩, rfl⟩ := ((finProdEquiv d E).trans e).surjective i
  obtain ⟨⟨u', t'⟩, rfl⟩ := ((finProdEquiv d E).trans e).surjective j
  simp only [Equiv.trans_apply]
  rw [kr_one_apply, Matrix.diagonal_apply, Matrix.diagonal_apply, hg]
  by_cases hu : u = u' <;> by_cases ht : t = t' <;> simp [hu, ht]

/-- A permutation acting along the second factor has the unitary `1 ⊗ τ`. -/
theorem permUnitary_eq_kr_one (e : Fin (d * E) ≃ Fin D) (π : Equiv.Perm (Fin D))
    (τ : Equiv.Perm (Fin E))
    (hπ : ∀ u t, π (e (finProdEquiv d E (u, t))) = e (finProdEquiv d E (u, τ t))) :
    (permUnitary π : Matrix (Fin D) (Fin D) ℂ) = kr e 1 (permUnitary τ) := by
  ext i j
  obtain ⟨⟨u, t⟩, rfl⟩ := ((finProdEquiv d E).trans e).surjective i
  obtain ⟨⟨u', t'⟩, rfl⟩ := ((finProdEquiv d E).trans e).surjective j
  simp only [Equiv.trans_apply]
  rw [kr_one_apply, permUnitary_apply, permUnitary_apply, hπ]
  simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hu : u = u' <;> simp [hu]

end KrForm

section Layout

variable (M n c a k w : ℕ) [NeZero M] [NeZero n] [NeZero c] [NeZero a]

/-- The work register of `permRound`: the work register of the adversary
followed by the slot register. -/
def workIndex : Fin (2 * w) × Fin (nfX c a k) ≃ Fin (2 * (w * nfX c a k)) :=
  (finProdEquiv (2 * w) (nfX c a k)).trans (finCongr (Nat.mul_assoc 2 w (nfX c a k)))

omit [NeZero a] in
/-- The padded index of a query, a work index and an extra-register state is the
`roundIndex` of the query, the work index followed by the slot register, and the
ancilla. -/
theorem padE_roundIndex
    (hW : 2 * w * (nfX c a k * ancDim M n c) = 2 * (w * nfX c a k) * ancDim M n c)
    (s : Fin M × Fin n) (z : Fin (2 * w)) (x : SlotReg c a k) (an : RoundAnc M n c) :
    padE M n hW (finProdEquiv _ _ (oracleIndex M n (2 * w) (s, z), extIndex M n c a k (x, an))) =
      roundIndex M n (2 * (w * nfX c a k)) c (s, workIndex c a k w (z, slotIndex c a k x), an) := by
  rw [roundIndex_apply]
  apply Fin.ext
  simp only [padE, finCongr_apply, Fin.val_cast, oracleIndex, ancFlat,
    extIndex, workIndex, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id,
    finProdEquiv, finProdFinEquiv_apply_val]
  ring

/-- The answer family of `permRound`: the shift of the answer register inside the
work register. -/
def nfAns (z : Fin a) : Equiv.Perm ((Fin M × Fin n) × Fin (2 * (w * nfX c a k))) :=
  (Equiv.refl _).prodCongr ((workIndex c a k w).permCongr ((Equiv.refl _).prodCongr
    ((slotIndex c a k).permCongr ((Equiv.addRight z).prodCongr (Equiv.refl _)))))

variable {M n c a k w}

/-- The record projector of `permRound` is `1 ⊗` the record projector of the
extra register. -/
theorem recProj_eq_kr
    (hW : 2 * w * (nfX c a k * ancDim M n c) = 2 * (w * nfX c a k) * ancDim M n c) (y : Fin c) :
    recProj M n (2 * (w * nfX c a k)) c y =
      kr (padE M n hW) 1 (indE fun t => (nfSlots M n c a k).recv t = y) := by
  rw [recProj, indE]
  refine diagonal_eq_kr_one _ _ _ fun u t => ?_
  obtain ⟨⟨s, z⟩, rfl⟩ := (oracleIndex M n (2 * w)).surjective u
  obtain ⟨⟨x, an⟩, rfl⟩ := (extIndex M n c a k).surjective t
  rw [padE_roundIndex]
  simp [cleanRec, nfSlots]

omit [NeZero a] in
/-- The clean projector is `1 ⊗` the projector onto the extra-register states
with parked slots `0`. -/
theorem cleanProjM_eq_kr_nf
    (hW : 2 * w * (nfX c a k * ancDim M n c) = 2 * (w * nfX c a k) * ancDim M n c) :
    cleanProjM M n (2 * (w * nfX c a k)) c = kr (padE M n hW) 1 (indE (nfClean M n c a k)) := by
  rw [cleanProjM, indE]
  refine diagonal_eq_kr_one _ _ _ fun u t => ?_
  obtain ⟨⟨s, z⟩, rfl⟩ := (oracleIndex M n (2 * w)).surjective u
  obtain ⟨⟨x, an⟩, rfl⟩ := (extIndex M n c a k).surjective t
  rw [padE_roundIndex]
  simp [IsClean, nfClean]

/-- The answer unitary of `permRound` at `z` is `1 ⊗` the shift of the answer
register by `z`. -/
theorem permUnitary_parkLift_nfAns
    (hW : 2 * w * (nfX c a k * ancDim M n c) = 2 * (w * nfX c a k) * ancDim M n c) (z : Fin a) :
    (permUnitary (parkLift M n (2 * (w * nfX c a k)) c (nfAns M n c a k w z)) :
        Matrix (Fin (M * n * (2 * (w * nfX c a k) * ancDim M n c)))
          (Fin (M * n * (2 * (w * nfX c a k) * ancDim M n c))) ℂ) =
      kr (padE M n hW) 1 (permUnitary ((nfSlots M n c a k).ansShift z)) := by
  refine permUnitary_eq_kr_one _ _ _ fun u t => ?_
  obtain ⟨⟨s, zz⟩, rfl⟩ := (oracleIndex M n (2 * w)).surjective u
  obtain ⟨⟨⟨x₁, x₂⟩, an⟩, rfl⟩ := (extIndex M n c a k).surjective t
  have hsh : (nfSlots M n c a k).ansShift z (extIndex M n c a k ((x₁, x₂), an)) =
      extIndex M n c a k ((x₁ + z, x₂), an) := by
    simp [nfSlots, Equiv.permCongr_apply]
  rw [hsh, padE_roundIndex, padE_roundIndex]
  simp [parkLift, parkLiftReg, Equiv.permCongr_apply, nfAns]

theorem ClassicalRound.ext' {d c' a' : ℕ} {R R' : ClassicalRound d c' a'} (hP : R.P = R'.P)
    (hans : R.ans = R'.ans) : R = R' := by
  cases R; cases R'; cases hP; cases hans; rfl

/-- **The fixed round of the normal form is `permRound`** in the `roundIndex`
layout, with the answer family `nfAns`. -/
theorem slotRound_eq_permRound
    (hW : 2 * w * (nfX c a k * ancDim M n c) = 2 * (w * nfX c a k) * ancDim M n c) :
    slotRound (padE M n hW) (nfSlots M n c a k) =
      permRound M n (2 * (w * nfX c a k)) c (nfAns M n c a k w) :=
  ClassicalRound.ext' (funext fun y => (recProj_eq_kr hW y).symm)
    (funext fun z => Subtype.ext (permUnitary_parkLift_nfAns hW z).symm)

theorem nfClean_recShift (y : Fin c) (t : Fin (nfX c a k * ancDim M n c)) :
    nfClean M n c a k ((nfSlots M n c a k).recShift y t) ↔ nfClean M n c a k t := by
  simp [nfClean, nfSlots, Equiv.permCongr_apply]

theorem nfClean_swap (j : ℕ) (t : Fin (nfX c a k * ancDim M n c)) :
    nfClean M n c a k ((nfSlots M n c a k).swap j t) ↔ nfClean M n c a k t := by
  simp only [nfClean, nfSlots, Equiv.permCongr_apply, Equiv.symm_apply_apply, swapR]
  split_ifs
  · simp [swapFun]
  · rfl

theorem nfClean_nfStart : nfClean M n c a k (nfStart M n c a k) := by
  simp [nfClean, nfStart]

end Layout

/-! ## The segments and the initial state on the clean slice -/

section CleanSeg

variable {d E D c a K : ℕ}

/-- `U` commutes with `1 ⊗ C`. -/
def CommKr (e : Fin (d * E) ≃ Fin D) (C : Matrix (Fin E) (Fin E) ℂ)
    (U : Matrix.unitaryGroup (Fin D) ℂ) : Prop :=
  (U : Matrix (Fin D) (Fin D) ℂ) * kr e 1 C = kr e 1 C * U

theorem commKr_mul {e : Fin (d * E) ≃ Fin D} {C : Matrix (Fin E) (Fin E) ℂ}
    {U V : Matrix.unitaryGroup (Fin D) ℂ} (hU : CommKr e C U) (hV : CommKr e C V) :
    CommKr e C (U * V) := by
  unfold CommKr at *
  show (U : Matrix (Fin D) (Fin D) ℂ) * V * _ = _ * ((U : Matrix (Fin D) (Fin D) ℂ) * V)
  rw [Matrix.mul_assoc, hV, ← Matrix.mul_assoc, hU, Matrix.mul_assoc]

theorem commKr_one (e : Fin (d * E) ≃ Fin D) (C : Matrix (Fin E) (Fin E) ℂ) : CommKr e C 1 := by
  unfold CommKr; simp

theorem commKr_liftU (e : Fin (d * E) ≃ Fin D) (C : Matrix (Fin E) (Fin E) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : CommKr e C (liftU e U) := by
  unfold CommKr
  rw [liftU_val, kr_mul, kr_mul, one_mul, mul_one, Matrix.one_mul, Matrix.mul_one]

theorem commKr_copyU (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K) (R : ClassicalRound d c a)
    (p : Fin E → Prop) [DecidablePred p] (hp : ∀ y t, p (S.recShift y t) ↔ p t) :
    CommKr e (indE p) (copyU e S R) := by
  unfold CommKr
  rw [copyU_val, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [kr_mul, kr_mul, mul_one, one_mul, permUnitary_mul_indE_comm _ _ (hp y)]

theorem commKr_ansCtrlU (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K) (j : ℕ)
    (R : ClassicalRound d c a) (p : Fin E → Prop) [DecidablePred p]
    (hp : ∀ t, p (S.swap j t) ↔ p t) : CommKr e (indE p) (ansCtrlU e S j R) := by
  refine commKr_mul ?_ ?_
  · unfold CommKr
    rw [liftE_val, kr_mul, kr_mul, Matrix.one_mul, permUnitary_mul_indE_comm _ _ hp]
  · unfold CommKr
    show ctrlE e S R * _ = _ * ctrlE e S R
    rw [ctrlE, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [kr_mul, kr_mul, mul_one, one_mul, indE_mul_indE_comm]

theorem backMul_of {d' : ℕ} (P : Matrix.unitaryGroup (Fin d') ℂ → Prop)
    (hmul : ∀ U V, P U → P V → P (U * V)) (V : Matrix.unitaryGroup (Fin d') ℂ) (hV : P V) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d') ℂ), (∀ i, P (U i)) →
      ∀ i, P (backMul V q U i)
  | 0, U, hU, _ => hmul _ _ hV (hU 0)
  | q + 1, U, hU, i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hU 0
    · exact backMul_of P hmul V hV q (Fin.tail U) (fun i => hU i.succ) i

theorem frontMul_of {d' q : ℕ} (P : Matrix.unitaryGroup (Fin d') ℂ → Prop)
    (hmul : ∀ U V, P U → P V → P (U * V)) (W : Matrix.unitaryGroup (Fin d') ℂ) (hW : P W)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d') ℂ) (hU : ∀ i, P (U i)) (i : Fin (q + 1)) :
    P (frontMul W U i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact hmul _ _ (hU 0) hW
  · exact hU i.succ

variable {m n W W' q k : ℕ}

/-- The segments of the normal form commute with `1 ⊗ indE p` for a predicate
`p` preserved by the record shifts and the swaps. -/
theorem nfMR_seg_comm (e : Fin (m * n * W * E) ≃ Fin (m * n * W')) (S : SlotData E c a k)
    (t₀ : Fin E) (A : QAdvMR m n W q k c a) (p : Fin E → Prop) [DecidablePred p]
    (hrec : ∀ y t, p (S.recShift y t) ↔ p t) (hswap : ∀ j t, p (S.swap j t) ↔ p t)
    (j : Fin (k + 1)) (i : Fin (q + 1)) :
    ((nfMR e S t₀ A).seg j i : Matrix (Fin (m * n * W')) (Fin (m * n * W')) ℂ) *
        kr e 1 (indE p) =
      kr e 1 (indE p) * ((nfMR e S t₀ A).seg j i : Matrix (Fin (m * n * W')) (Fin (m * n * W')) ℂ) := by
  have hmul : ∀ U V, CommKr e (indE p) U → CommKr e (indE p) V → CommKr e (indE p) (U * V) :=
    fun _ _ => commKr_mul
  refine frontMul_of (CommKr e (indE p)) hmul _ ?_ _ (backMul_of _ hmul _ ?_ q _
    (fun i => commKr_liftU e _ _)) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact commKr_one e _
    · simp only [nfW, Fin.cases_succ]
      exact commKr_ansCtrlU e S j (A.rounds j) p (hswap j)
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [nfV, Fin.lastCases_last]
      exact commKr_one e _
    · simp only [nfV, Fin.lastCases_castSucc]
      exact commKr_copyU e S (A.rounds j) p hrec

/-- The initial state of the normal form is supported on `1 ⊗ indE p` when `p`
holds at `t₀`. -/
theorem nfMR_init_supported (e : Fin (m * n * W * E) ≃ Fin (m * n * W')) (S : SlotData E c a k)
    (t₀ : Fin E) (A : QAdvMR m n W q k c a) (p : Fin E → Prop) [DecidablePred p] (hp : p t₀) :
    SupportedOn (kr e 1 (indE p)) (nfMR e S t₀ A).init.val := by
  rw [SupportedOn]
  show kr e 1 (indE p) * kr e A.init.val (ancProj t₀) * kr e 1 (indE p) =
    kr e A.init.val (ancProj t₀)
  rw [kr_mul, kr_mul, Matrix.one_mul, Matrix.mul_one, ← ancUnit_self, indE_mul_ancUnit,
    if_pos hp, ancUnit_mul_indE, if_pos hp]

end CleanSeg

/-! ## The normal form of a KEM adversary -/

section KEM

theorem ancProj_eq_vecMulVec {c : ℕ} (t : Fin c) :
    ancProj t = vecMulVec (Pi.single t 1) (star (Pi.single t 1)) := by
  ext i j
  simp only [ancProj, Matrix.diagonal_apply, vecMulVec_apply, Pi.star_apply, Pi.single_apply]
  by_cases hi : i = t
  · subst hi
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj, Ne.symm hj]
  · simp [hi]

variable {m₁ m₂ n w q k c a : ℕ} {PK C K : Type} [NeZero (m₁ + m₂)] [NeZero n] [NeZero c]
  [NeZero a]

/-- The normal form of a KEM adversary: `nfMR` of every run, on the work register
`w * (nfX c a k * ancDim …)`. -/
def nfKEM (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    KEMQAdv m₁ m₂ n (w * (nfX c a k * ancDim (m₁ + m₂) n c)) q k c a PK C K where
  run pk cs κ := nfMR (padE (m₁ + m₂) n (Nat.mul_assoc 2 w (nfX c a k * ancDim (m₁ + m₂) n c)))
    (nfSlots (m₁ + m₂) n c a k) (nfStart (m₁ + m₂) n c a k) (A.run pk cs κ)
  final_eq pk cs κ := by
    show kr _ (A.run pk cs κ).final 1 = _
    rw [A.final_eq, winBitProj_pad]
  pure pk cs κ := by
    obtain ⟨ψ, hψ⟩ := A.pure pk cs κ
    exact ⟨_, show kr _ (A.run pk cs κ).init.val (ancProj _) = _ by
      rw [hψ, ancProj_eq_vecMulVec, kr_vecMulVec]⟩

omit [NeZero (m₁ + m₂)] [NeZero n] [NeZero c] [NeZero a] in
/-- The work-register identity placing the ancilla of `permRound` last. -/
theorem nfKEM_hw (w c a k m : ℕ) :
    2 * (w * (nfX c a k * ancDim m n c)) = 2 * (w * nfX c a k) * ancDim m n c := by
  ring

theorem castMR_nfKEM (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (pk : PK) (cs : C) (κ : K) :
    castMR (nfKEM_hw w c a k (m₁ + m₂)) ((nfKEM A).run pk cs κ) =
      nfMR (padE (m₁ + m₂) n ((Nat.mul_assoc 2 w _).trans (nfKEM_hw w c a k (m₁ + m₂))))
        (nfSlots (m₁ + m₂) n c a k) (nfStart (m₁ + m₂) n c a k) (A.run pk cs κ) :=
  castMR_nfMR _ _ _ _ _

/-- The segments of `nfKEM A` commute with `cleanProjM`. -/
theorem nfKEM_hseg (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (pk : PK) (cs : C) (κ : K)
    (j : Fin (k + 1)) (i : Fin (q + 1)) :
    ((castMR (nfKEM_hw w c a k (m₁ + m₂)) ((nfKEM A).run pk cs κ)).seg j i : Matrix _ _ ℂ) *
        cleanProjM (m₁ + m₂) n (2 * (w * nfX c a k)) c =
      cleanProjM (m₁ + m₂) n (2 * (w * nfX c a k)) c *
        ((castMR (nfKEM_hw w c a k (m₁ + m₂)) ((nfKEM A).run pk cs κ)).seg j i : Matrix _ _ ℂ) := by
  rw [castMR_nfKEM, cleanProjM_eq_kr_nf ((Nat.mul_assoc 2 w _).trans (nfKEM_hw w c a k (m₁ + m₂)))]
  exact nfMR_seg_comm _ _ _ _ _ nfClean_recShift nfClean_swap j i

/-- Every round of `nfKEM A` is `permRound` with the answer family `nfAns`. -/
theorem nfKEM_hrounds (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (pk : PK) (cs : C) (κ : K)
    (j : Fin k) :
    (castMR (nfKEM_hw w c a k (m₁ + m₂)) ((nfKEM A).run pk cs κ)).rounds j =
      permRound (m₁ + m₂) n (2 * (w * nfX c a k)) c (nfAns (m₁ + m₂) n c a k w) := by
  rw [castMR_nfKEM]
  exact slotRound_eq_permRound _

/-- The initial state of `nfKEM A` is supported on the clean slice. -/
theorem nfKEM_hinit (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (pk : PK) (cs : C) (κ : K) :
    SupportedOn (cleanProjM (m₁ + m₂) n (2 * (w * nfX c a k)) c)
      (castMR (nfKEM_hw w c a k (m₁ + m₂)) ((nfKEM A).run pk cs κ)).init.val := by
  rw [castMR_nfKEM, cleanProjM_eq_kr_nf ((Nat.mul_assoc 2 w _).trans (nfKEM_hw w c a k (m₁ + m₂)))]
  exact nfMR_init_supported _ _ _ _ _ nfClean_nfStart

variable {SK M R Hash Z : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype Z] [Fintype K]
  [Nonempty K] [DecidableEq C] (P : Scheme PK SK M C R) (hpk : PK → Hash)
  (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c)
  (eKa : K ≃ Fin a)

/-- The normal form leaves the winning probability unchanged. -/
theorem prWinKEM_nfKEM (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinKEM P hpk eG eJ eKR eC eKa (nfKEM A) b = prWinKEM P hpk eG eJ eKR eC eKa A b := by
  unfold prWinKEM
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nfKEM, prOutMR_nfMR _ _ _ (nfStart_good (m₁ + m₂) n c a k)]

/-- The normal form leaves the IND-CCA advantage unchanged. -/
theorem qINDCCAAdvantage_nfKEM (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    qINDCCAAdvantage P hpk eG eJ eKR eC eKa (nfKEM A) =
      qINDCCAAdvantage P hpk eG eJ eKR eC eKa A := by
  rw [qINDCCAAdvantage, qINDCCAAdvantage, prWinKEM_nfKEM, prWinKEM_nfKEM]

end KEM

end CatCrypt.Quantum.QROM

end

end
