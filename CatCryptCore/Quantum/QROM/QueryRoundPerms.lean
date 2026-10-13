/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.PermUnitaryCore
public import CatCryptCore.Quantum.QROM.FindToGuess

/-!
# A decapsulation round as four oracle queries on one clean ancilla

A round whose classical function `f` reads the oracle at two points determined
by the recorded ciphertext, `f r = φ r (H (ν₁ r)) (H (ν₂ r))`, is compiled into
four applications of the oracle permutation separated by five oracle-independent
permutations of the register index. The register carries, beside the query
register `Fin m × Fin n` and the work register `Fin w`, an ancilla holding a
ciphertext record `Fin c` and two parked query slots `Fin m × Fin n`.

## Main definitions

* `RoundAnc`, `RoundReg` — the ancilla and the full register as product types
* `ancDim`, `ancIndex`, `ancFlat`, `roundIndex` — the row-major index of the
  full register in `Fin (m * n * (w * ancDim m n c))`
* `swapPark`, `writeQuery`, `negateValue`, `answerPerm`, `recordPerm`,
  `unrecordPerm` — the six oracle-independent permutations of that index
* `stepZero`, `stepOne`, `stepTwo`, `stepThree`, `stepFour` — the five
  permutations of the query chain
* `roundPerm` — the chain
  `stepFour ∘ O ∘ stepThree ∘ O ∘ stepTwo ∘ O ∘ stepOne ∘ O ∘ stepZero` for the
  oracle permutation `O` of `H`

## Main results

* `oraclePerm_roundIndex` — the oracle permutation acts on the value factor of
  the query register and fixes the work register and the ancilla
* `swapPark_apply_false`, `swapPark_apply_true`, `writeQuery_apply`,
  `writeQuery_inv_apply`, `negateValue_apply`, `answerPerm_apply`,
  `recordPerm_apply`, `unrecordPerm_apply` — each permutation on a structured
  index
* `swapPark_mul_self`, `negateValue_mul_self` — the two involutions
* `unrecordPerm_mul_recordPerm` — the record and its removal cancel
* `stepZero_apply`, `stepOne_apply`, `stepTwo_apply`, `stepThree_apply`,
  `stepFour_apply` — each step of the chain on a structured index
* `roundPerm_eq_mul`, `roundPerm_front_apply_clean`, `roundPerm_back_apply` —
  the chain split after its second query, and each half on a structured index
* `roundPerm_apply_clean` — on an index whose two parked slots are `0` and whose
  record slot is `r`, the chain acts on the query and work registers by
  `A (φ r (H (ν₁ r)) (H (ν₂ r)))` and returns the parked slots to `0`

## Scope

Everything here is an identity of index maps: permutations of
`Fin (m * n * (w * ancDim m n c))` and their values, with no matrix and no
unitary. The answer family `A` is a family of permutations of the query and work
registers, the permutation form of the answer unitaries of a classical round.
The oracle enters only through `oraclePerm`, and every other factor of the chain
is independent of `H`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CatCrypt.Quantum CatCrypt.Quantum.TensorProduct

noncomputable section

namespace CatCrypt.Quantum.QROM

variable (m n w c : ℕ) [NeZero m] [NeZero n] [NeZero c]

/-! ## The register and its index -/

/-- The ancilla of a query round: a ciphertext record and two parked query
    slots. -/
abbrev RoundAnc : Type := Fin c × (Fin m × Fin n) × (Fin m × Fin n)

/-- The full register of a query round: the query register, the work register
    and the ancilla. -/
abbrev RoundReg : Type := (Fin m × Fin n) × Fin w × RoundAnc m n c

/-- The dimension of the ancilla `RoundAnc m n c`. -/
def ancDim : ℕ := c * (m * n) * (m * n)

/-- The row-major index of the ancilla in `Fin (ancDim m n c)`. -/
def ancIndex : RoundAnc m n c ≃ Fin (ancDim m n c) :=
  (((Equiv.refl (Fin c)).prodCongr
        ((finProdEquiv m n).prodCongr (finProdEquiv m n))).trans
      (Equiv.prodAssoc (Fin c) (Fin (m * n)) (Fin (m * n))).symm).trans
    (((finProdEquiv c (m * n)).prodCongr (Equiv.refl (Fin (m * n)))).trans
      (finProdEquiv (c * (m * n)) (m * n)))

/-- The row-major index of the work register together with the ancilla. -/
def ancFlat : Fin w × RoundAnc m n c ≃ Fin (w * ancDim m n c) :=
  ((Equiv.refl (Fin w)).prodCongr (ancIndex m n c)).trans (finProdEquiv w (ancDim m n c))

/-- The row-major index of the full register in
    `Fin (m * n * (w * ancDim m n c))`. -/
def roundIndex : RoundReg m n w c ≃ Fin (m * n * (w * ancDim m n c)) :=
  ((Equiv.refl (Fin m × Fin n)).prodCongr (ancFlat m n w c)).trans
    (oracleIndex m n (w * ancDim m n c))

theorem roundIndex_apply (s : RoundReg m n w c) :
    roundIndex m n w c s =
      oracleIndex m n (w * ancDim m n c) (s.1, ancFlat m n w c s.2) := rfl

/-- The oracle permutation adds `H x` to the value factor of the query register
    and fixes the work register and the ancilla. -/
theorem oraclePerm_roundIndex (H : Fin m → Fin n) (x : Fin m) (y : Fin n)
    (z : Fin w) (e : RoundAnc m n c) :
    oraclePerm m n (w * ancDim m n c) H (roundIndex m n w c ((x, y), z, e)) =
      roundIndex m n w c ((x, y + H x), z, e) := by
  rw [roundIndex_apply, roundIndex_apply, oraclePerm_apply]

/-! ## The six oracle-independent permutations -/

/-- The exchange of the query register with the first (`false`) or the second
    (`true`) parked slot, on the structured register. -/
def swapParkReg : Bool → Equiv.Perm (RoundReg m n w c)
  | false =>
    ⟨fun (q, z, r, p₁, p₂) => (p₁, z, r, q, p₂),
      fun (q, z, r, p₁, p₂) => (p₁, z, r, q, p₂),
      by rintro ⟨q, z, r, p₁, p₂⟩; rfl, by rintro ⟨q, z, r, p₁, p₂⟩; rfl⟩
  | true =>
    ⟨fun (q, z, r, p₁, p₂) => (p₂, z, r, p₁, q),
      fun (q, z, r, p₁, p₂) => (p₂, z, r, p₁, q),
      by rintro ⟨q, z, r, p₁, p₂⟩; rfl, by rintro ⟨q, z, r, p₁, p₂⟩; rfl⟩

/-- The exchange of the query register with a parked slot. -/
def swapPark (i : Bool) : Equiv.Perm (Fin (m * n * (w * ancDim m n c))) :=
  (roundIndex m n w c).permCongr (swapParkReg m n w c i)

/-- The addition of `ν r`, read from the record slot, to the query factor of the
    query register, on the structured register. -/
def writeQueryReg (ν : Fin c → Fin m) : Equiv.Perm (RoundReg m n w c) where
  toFun := fun (q, z, r, p) => ((q.1 + ν r, q.2), z, r, p)
  invFun := fun (q, z, r, p) => ((q.1 - ν r, q.2), z, r, p)
  left_inv := by rintro ⟨⟨a, b⟩, z, r, p⟩; simp
  right_inv := by rintro ⟨⟨a, b⟩, z, r, p⟩; simp

/-- The addition of `ν r`, read from the record slot, to the query factor of the
    query register. -/
def writeQuery (ν : Fin c → Fin m) : Equiv.Perm (Fin (m * n * (w * ancDim m n c))) :=
  (roundIndex m n w c).permCongr (writeQueryReg m n w c ν)

/-- The negation of the value factor of the query register, on the structured
    register. -/
def negateValueReg : Equiv.Perm (RoundReg m n w c) :=
  ⟨fun (q, z, e) => ((q.1, -q.2), z, e), fun (q, z, e) => ((q.1, -q.2), z, e),
    by rintro ⟨⟨a, b⟩, z, e⟩; simp, by rintro ⟨⟨a, b⟩, z, e⟩; simp⟩

/-- The negation of the value factor of the query register. -/
def negateValue : Equiv.Perm (Fin (m * n * (w * ancDim m n c))) :=
  (roundIndex m n w c).permCongr (negateValueReg m n w c)

variable {a : ℕ}

/-- The answer permutation `A (φ r v₁ v₂)` applied to the first parked slot and
    the work register, controlled on the record slot, on the value factor of the
    second parked slot and on the value factor of the query register, on the
    structured register. -/
def answerReg (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) : Equiv.Perm (RoundReg m n w c) where
  toFun := fun (q, z, r, p₁, p₂) =>
    (q, (A (φ r p₂.2 q.2) (p₁, z)).2, r, (A (φ r p₂.2 q.2) (p₁, z)).1, p₂)
  invFun := fun (q, z, r, p₁, p₂) =>
    (q, ((A (φ r p₂.2 q.2)).symm (p₁, z)).2, r, ((A (φ r p₂.2 q.2)).symm (p₁, z)).1, p₂)
  left_inv := by rintro ⟨q, z, r, p₁, p₂⟩; simp
  right_inv := by rintro ⟨q, z, r, p₁, p₂⟩; simp

/-- The answer permutation, controlled on the record slot and the two parked
    values. -/
def answerPerm (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) :
    Equiv.Perm (Fin (m * n * (w * ancDim m n c))) :=
  (roundIndex m n w c).permCongr (answerReg m n w c φ A)

variable {m n w c}

/-- The addition of the ciphertext `cf` of the query and work registers to the
    record slot, on the structured register. -/
def recordReg (cf : (Fin m × Fin n) × Fin w → Fin c) : Equiv.Perm (RoundReg m n w c) where
  toFun := fun (q, z, r, p) => (q, z, r + cf (q, z), p)
  invFun := fun (q, z, r, p) => (q, z, r - cf (q, z), p)
  left_inv := by rintro ⟨q, z, r, p⟩; simp
  right_inv := by rintro ⟨q, z, r, p⟩; simp

/-- The subtraction of the ciphertext `cf` of the query and work registers from
    the record slot, on the structured register. -/
def unrecordReg (cf : (Fin m × Fin n) × Fin w → Fin c) : Equiv.Perm (RoundReg m n w c) :=
  (recordReg cf).symm

variable (m n w c)

/-- The addition of the ciphertext of the query and work registers to the record
    slot. -/
def recordPerm (cf : (Fin m × Fin n) × Fin w → Fin c) :
    Equiv.Perm (Fin (m * n * (w * ancDim m n c))) :=
  (roundIndex m n w c).permCongr (recordReg cf)

/-- The subtraction of the ciphertext of the query and work registers from the
    record slot. -/
def unrecordPerm (cf : (Fin m × Fin n) × Fin w → Fin c) :
    Equiv.Perm (Fin (m * n * (w * ancDim m n c))) :=
  (roundIndex m n w c).permCongr (unrecordReg cf)

/-! ## The action of each permutation on a structured index -/

theorem swapPark_apply_false (q : Fin m × Fin n) (z : Fin w) (r : Fin c)
    (p₁ p₂ : Fin m × Fin n) :
    swapPark m n w c false (roundIndex m n w c (q, z, r, p₁, p₂)) =
      roundIndex m n w c (p₁, z, r, q, p₂) := by
  simp [swapPark, swapParkReg, Equiv.permCongr_apply]

theorem swapPark_apply_true (q : Fin m × Fin n) (z : Fin w) (r : Fin c)
    (p₁ p₂ : Fin m × Fin n) :
    swapPark m n w c true (roundIndex m n w c (q, z, r, p₁, p₂)) =
      roundIndex m n w c (p₂, z, r, p₁, q) := by
  simp [swapPark, swapParkReg, Equiv.permCongr_apply]

theorem writeQuery_apply (ν : Fin c → Fin m) (x : Fin m) (y : Fin n) (z : Fin w)
    (r : Fin c) (p : (Fin m × Fin n) × (Fin m × Fin n)) :
    writeQuery m n w c ν (roundIndex m n w c ((x, y), z, r, p)) =
      roundIndex m n w c ((x + ν r, y), z, r, p) := by
  simp [writeQuery, writeQueryReg, Equiv.permCongr_apply]

theorem writeQuery_inv_apply (ν : Fin c → Fin m) (x : Fin m) (y : Fin n) (z : Fin w)
    (r : Fin c) (p : (Fin m × Fin n) × (Fin m × Fin n)) :
    (writeQuery m n w c ν)⁻¹ (roundIndex m n w c ((x, y), z, r, p)) =
      roundIndex m n w c ((x - ν r, y), z, r, p) := by
  rw [Equiv.Perm.inv_eq_iff_eq, writeQuery_apply]
  simp

theorem negateValue_apply (x : Fin m) (y : Fin n) (z : Fin w) (e : RoundAnc m n c) :
    negateValue m n w c (roundIndex m n w c ((x, y), z, e)) =
      roundIndex m n w c ((x, -y), z, e) := by
  simp [negateValue, negateValueReg, Equiv.permCongr_apply]

theorem answerPerm_apply (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (q : Fin m × Fin n) (z : Fin w)
    (r : Fin c) (p₁ p₂ : Fin m × Fin n) :
    answerPerm m n w c φ A (roundIndex m n w c (q, z, r, p₁, p₂)) =
      roundIndex m n w c
        (q, (A (φ r p₂.2 q.2) (p₁, z)).2, r, (A (φ r p₂.2 q.2) (p₁, z)).1, p₂) := by
  simp [answerPerm, answerReg, Equiv.permCongr_apply]

theorem recordPerm_apply (cf : (Fin m × Fin n) × Fin w → Fin c) (q : Fin m × Fin n)
    (z : Fin w) (r : Fin c) (p : (Fin m × Fin n) × (Fin m × Fin n)) :
    recordPerm m n w c cf (roundIndex m n w c (q, z, r, p)) =
      roundIndex m n w c (q, z, r + cf (q, z), p) := by
  simp [recordPerm, recordReg, Equiv.permCongr_apply]

theorem unrecordPerm_apply (cf : (Fin m × Fin n) × Fin w → Fin c) (q : Fin m × Fin n)
    (z : Fin w) (r : Fin c) (p : (Fin m × Fin n) × (Fin m × Fin n)) :
    unrecordPerm m n w c cf (roundIndex m n w c (q, z, r, p)) =
      roundIndex m n w c (q, z, r - cf (q, z), p) := by
  simp [unrecordPerm, unrecordReg, recordReg, Equiv.permCongr_apply]

/-! ## The involutions and the record cancellation -/

theorem swapParkReg_involutive (i : Bool) :
    Function.Involutive (swapParkReg m n w c i) := by
  rintro ⟨q, z, r, p₁, p₂⟩
  cases i <;> rfl

theorem swapPark_mul_self (i : Bool) :
    swapPark m n w c i * swapPark m n w c i = 1 := by
  ext k
  simp [swapPark, Equiv.Perm.mul_apply, Equiv.permCongr_apply, swapParkReg_involutive m n w c i _]

theorem negateValueReg_involutive :
    Function.Involutive (negateValueReg m n w c) := by
  rintro ⟨⟨x, y⟩, z, e⟩
  simp [negateValueReg]

theorem negateValue_mul_self : negateValue m n w c * negateValue m n w c = 1 := by
  ext k
  simp [negateValue, Equiv.Perm.mul_apply, Equiv.permCongr_apply,
    negateValueReg_involutive m n w c _]

theorem unrecordPerm_mul_recordPerm (cf : (Fin m × Fin n) × Fin w → Fin c) :
    unrecordPerm m n w c cf * recordPerm m n w c cf = 1 := by
  ext k
  simp [unrecordPerm, recordPerm, unrecordReg, Equiv.Perm.mul_apply, Equiv.permCongr_apply]

/-! ## The query chain -/

variable (ν₁ ν₂ : Fin c → Fin m)

/-- The first step: park the query register and write `ν₁` from the record. -/
def stepZero : Equiv.Perm (Fin (m * n * (w * ancDim m n c))) :=
  writeQuery m n w c ν₁ * swapPark m n w c false

/-- The second step: park the first oracle answer and write `ν₂` from the
    record. -/
def stepOne : Equiv.Perm (Fin (m * n * (w * ancDim m n c))) :=
  writeQuery m n w c ν₂ * swapPark m n w c true

/-- The third step: answer, then negate the value factor for the first
    uncomputing query. -/
def stepTwo (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) :
    Equiv.Perm (Fin (m * n * (w * ancDim m n c))) :=
  negateValue m n w c * answerPerm m n w c φ A

/-- The fourth step: clear the second query point, restore the first oracle
    answer and negate its value factor for the second uncomputing query. -/
def stepThree : Equiv.Perm (Fin (m * n * (w * ancDim m n c))) :=
  negateValue m n w c * swapPark m n w c true * (writeQuery m n w c ν₂)⁻¹

/-- The fifth step: clear the first query point and restore the query
    register. -/
def stepFour : Equiv.Perm (Fin (m * n * (w * ancDim m n c))) :=
  swapPark m n w c false * (writeQuery m n w c ν₁)⁻¹

theorem stepZero_apply (q : Fin m × Fin n) (z : Fin w) (r : Fin c) (u : Fin m) (v : Fin n)
    (p₂ : Fin m × Fin n) :
    stepZero m n w c ν₁ (roundIndex m n w c (q, z, r, (u, v), p₂)) =
      roundIndex m n w c ((u + ν₁ r, v), z, r, q, p₂) := by
  simp only [stepZero, Equiv.Perm.mul_apply, swapPark_apply_false, writeQuery_apply]

theorem stepOne_apply (q : Fin m × Fin n) (z : Fin w) (r : Fin c) (p₁ : Fin m × Fin n)
    (u : Fin m) (v : Fin n) :
    stepOne m n w c ν₂ (roundIndex m n w c (q, z, r, p₁, (u, v))) =
      roundIndex m n w c ((u + ν₂ r, v), z, r, p₁, q) := by
  simp only [stepOne, Equiv.Perm.mul_apply, swapPark_apply_true, writeQuery_apply]

theorem stepTwo_apply (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (x : Fin m) (y : Fin n) (z : Fin w)
    (r : Fin c) (p₁ : Fin m × Fin n) (u : Fin m) (v : Fin n) :
    stepTwo m n w c φ A (roundIndex m n w c ((x, y), z, r, p₁, (u, v))) =
      roundIndex m n w c
        ((x, -y), (A (φ r v y) (p₁, z)).2, r, (A (φ r v y) (p₁, z)).1, (u, v)) := by
  simp only [stepTwo, Equiv.Perm.mul_apply, answerPerm_apply, negateValue_apply]

theorem stepThree_apply (x : Fin m) (y : Fin n) (z : Fin w) (r : Fin c)
    (p₁ : Fin m × Fin n) (u : Fin m) (v : Fin n) :
    stepThree m n w c ν₂ (roundIndex m n w c ((x, y), z, r, p₁, (u, v))) =
      roundIndex m n w c ((u, -v), z, r, p₁, (x - ν₂ r, y)) := by
  simp only [stepThree, Equiv.Perm.mul_apply, writeQuery_inv_apply, swapPark_apply_true,
    negateValue_apply]

theorem stepFour_apply (x : Fin m) (y : Fin n) (z : Fin w) (r : Fin c)
    (p₁ p₂ : Fin m × Fin n) :
    stepFour m n w c ν₁ (roundIndex m n w c ((x, y), z, r, p₁, p₂)) =
      roundIndex m n w c (p₁, z, r, (x - ν₁ r, y), p₂) := by
  simp only [stepFour, Equiv.Perm.mul_apply, writeQuery_inv_apply, swapPark_apply_false]

/-- The round as four oracle queries separated by the five oracle-independent
    steps. -/
def roundPerm (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n) :
    Equiv.Perm (Fin (m * n * (w * ancDim m n c))) :=
  stepFour m n w c ν₁ * oraclePerm m n (w * ancDim m n c) H *
    stepThree m n w c ν₂ * oraclePerm m n (w * ancDim m n c) H *
    stepTwo m n w c φ A * oraclePerm m n (w * ancDim m n c) H *
    stepOne m n w c ν₂ * oraclePerm m n (w * ancDim m n c) H *
    stepZero m n w c ν₁

/-- The chain split after its second query. -/
theorem roundPerm_eq_mul (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n) :
    roundPerm m n w c ν₁ ν₂ φ A H =
      (stepFour m n w c ν₁ * oraclePerm m n (w * ancDim m n c) H *
          stepThree m n w c ν₂ * oraclePerm m n (w * ancDim m n c) H) *
        (stepTwo m n w c φ A * oraclePerm m n (w * ancDim m n c) H *
          stepOne m n w c ν₂ * oraclePerm m n (w * ancDim m n c) H *
          stepZero m n w c ν₁) := by
  simp only [roundPerm, mul_assoc]

/-- The first two queries and their three steps, on a clean index. -/
theorem roundPerm_front_apply_clean (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (q : Fin m × Fin n) (z : Fin w) (r : Fin c) :
    (stepTwo m n w c φ A * oraclePerm m n (w * ancDim m n c) H *
        stepOne m n w c ν₂ * oraclePerm m n (w * ancDim m n c) H * stepZero m n w c ν₁)
        (roundIndex m n w c (q, z, r, (0, 0), (0, 0))) =
      roundIndex m n w c ((ν₂ r, -H (ν₂ r)),
        (A (φ r (H (ν₁ r)) (H (ν₂ r))) (q, z)).2, r,
        (A (φ r (H (ν₁ r)) (H (ν₂ r))) (q, z)).1, (ν₁ r, H (ν₁ r))) := by
  simp only [Equiv.Perm.mul_apply, stepZero_apply, stepOne_apply, stepTwo_apply,
    oraclePerm_roundIndex, zero_add]

/-- The last two queries and their two steps: they clear both parked slots. -/
theorem roundPerm_back_apply (H : Fin m → Fin n) (z : Fin w) (r : Fin c)
    (p : Fin m × Fin n) :
    (stepFour m n w c ν₁ * oraclePerm m n (w * ancDim m n c) H *
        stepThree m n w c ν₂ * oraclePerm m n (w * ancDim m n c) H)
        (roundIndex m n w c ((ν₂ r, -H (ν₂ r)), z, r, p, (ν₁ r, H (ν₁ r)))) =
      roundIndex m n w c (p, z, r, (0, 0), (0, 0)) := by
  simp only [Equiv.Perm.mul_apply, oraclePerm_roundIndex, neg_add_cancel, stepThree_apply,
    sub_self, stepFour_apply]

/-- On an index whose two parked slots are `0` and whose record slot is `r`, the
    chain acts on the query and work registers by `A (φ r (H (ν₁ r)) (H (ν₂ r)))`
    and returns the parked slots to `0`. -/
theorem roundPerm_apply_clean (φ : Fin c → Fin n → Fin n → Fin a)
    (A : Fin a → Equiv.Perm ((Fin m × Fin n) × Fin w)) (H : Fin m → Fin n)
    (q : Fin m × Fin n) (z : Fin w) (r : Fin c) :
    roundPerm m n w c ν₁ ν₂ φ A H (roundIndex m n w c (q, z, r, (0, 0), (0, 0))) =
      roundIndex m n w c
        ((A (φ r (H (ν₁ r)) (H (ν₂ r))) (q, z)).1,
          (A (φ r (H (ν₁ r)) (H (ν₂ r))) (q, z)).2, r, (0, 0), (0, 0)) := by
  rw [roundPerm_eq_mul, Equiv.Perm.mul_apply, roundPerm_front_apply_clean,
    roundPerm_back_apply]

end CatCrypt.Quantum.QROM
