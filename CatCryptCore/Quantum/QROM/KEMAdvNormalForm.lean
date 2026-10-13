/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.DeltaStarLeLambda

/-!
# Padding a KEM adversary with the round ancilla

The numeric bound `qINDCCA_le_find_numeric` reads the work register of the
adversary as `w₀` work qubits followed by the ancilla `RoundAnc` of the compiled
decapsulation rounds, and assumes that the
segment unitaries leave the parked query slots of that ancilla alone and that
the initial state has them at `0`. Any adversary is brought into this shape
by tensoring every segment unitary, every round and the final projector with
the identity on a fresh ancilla `Fin (ancDim …)` and the initial state with
`|0⟩⟨0|`. The ancilla is never touched, so the output probability, and with it
the IND-CCA advantage, is unchanged.

## Main definitions

* `padE hW` — the index equivalence `Fin (m * n * W * D) ≃ Fin (m * n * W')`
  for `W * D = W'`
* `liftMR e A` — the multi-round adversary `A ⊗ 1` with initial state
  `ρ ⊗ |0⟩⟨0|`
* `ancCleanProj m n c` — the projector onto the ancilla states whose parked
  slots are `0`
* `padAdv A` — the KEM adversary `A` on the work register `w * ancDim …`
* `recRound e R` — the round measuring a record ancilla in the computational
  basis and answering by the answers of `R`
* `xorRound e R`, `ctrlAns e R` — the round answering `k` by a shift of an
  answer register, and the answers of `R` controlled on that register

## Main results

* `prOutMR_liftMR` — the lifted adversary outputs `1` with the probability of `A`
* `winBitProj_pad` — the output projector on the padded register is the lift
  of the output projector
* `cleanProjM_eq_kr` — `cleanProjM` is `1 ⊗ ancCleanProj`
* `qINDCCAAdvantage_padAdv` — padding leaves the IND-CCA advantage unchanged
* `padAdv_hseg`, `padAdv_hinit` — the padded adversary satisfies the segment
  and initial-state hypotheses of `qINDCCA_le_find_numeric` at `w₀ = 2 * w`
* `trace_normalForm_round` — one classical round `R`, with an arbitrary
  projector family and arbitrary answer unitaries, is reproduced on every
  observable `X ⊗ 1 ⊗ 1` by: the copy `roundW` of its outcome into a record,
  a round that measures the record in the computational basis and answers by a
  shift, and the controlled answer `ctrlAns`

## Scope

The rounds of `padAdv A` are the rounds of `A` tensored with the identity, so
they are not of the form `permRound` when `A` has rounds: `permRound` measures
the record slot of the ancilla, which `padAdv A` never touches. The hypothesis
`hrounds` of `qINDCCA_le_find_numeric` holds for `padAdv A` only at `k = 0`.

`trace_normalForm_round` is a single round on an abstract Kronecker layout
`d ⊗ c ⊗ a`. The multi-round form, with the record and the answer register of
round `j` swapped into fresh work slots before round `j + 1`, and its placement
in the `roundIndex` layout of `permRound`, is `nfKEM` in
`Quantum/QROM/KEMAdvNormalFormMR.lean`.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
  CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Lifting a multi-round adversary along an ancilla -/

section Lift

variable {m n W W' D q k c a : ℕ}

/-- The round with every projector and answer tensored with `1` on an ancilla
`Fin D` of any dimension. -/
def liftRA {d d' : ℕ} (e : Fin (d * D) ≃ Fin d') (R : ClassicalRound d c a) :
    ClassicalRound d' c a where
  P y := kr e (R.P y) 1
  P_conjTranspose y := by rw [kr_conjTranspose, R.P_conjTranspose, conjTranspose_one]
  P_mul_self y := by rw [kr_mul, R.P_mul_self, one_mul]
  P_orth y y' h := by rw [kr_mul, R.P_orth y y' h, kr_zero_left]
  P_sum := by rw [← kr_sum_left, R.P_sum, kr_one]
  ans z := liftU e (R.ans z)

theorem liftsQ_roundU_liftRA {d d' : ℕ} (e : Fin (d * D) ≃ Fin d') (R : ClassicalRound d c a)
    (f : Fin c → Fin a) : LiftsQ e (roundU R f) (roundU (liftRA e R) f) := by
  intro _ B E
  rw [roundU_branch, roundU_branch, kr_sum_left]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [liftRA, liftU_val]
  rw [kr_mul, kr_conjTranspose, kr_mul, kr_mul]
  simp

/-- The multi-round chain over the lifted segments and rounds lifts the
multi-round chain, for an ancilla of any dimension. -/
theorem liftsQ_mrChainSC_liftRA {d d' : ℕ} (e : Fin (d * D) ≃ Fin d') (O : QComp d Bool)
    (O' : QComp d' Bool) (hO : LiftsQ e O O') (f : Fin c → Fin a) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin k → ClassicalRound d c a) :
    LiftsQ e (mrChainSC O f k q₀ head tail R)
      (mrChainSC O' f k q₀ (liftU e ∘ head) (fun j => liftU e ∘ tail j) (liftRA e ∘ R)) := by
  induction k generalizing q₀ head with
  | zero => exact liftsQ_scChain e O O' hO q₀ head
  | succ k ih =>
    exact liftsQ_qbind e (liftsQ_scChain e O O' hO q₀ head) fun b =>
      liftsQ_qbind e (liftsQ_roundU_liftRA e (R 0) f) fun _ =>
        liftsQ_qbind e (ih q (tail 0) (Fin.tail tail) (Fin.tail R)) fun b' => liftsQ_qpure e _

/-- The index equivalence `Fin (m * n * W * D) ≃ Fin (m * n * W')` for
`W * D = W'`. -/
def padE (m n : ℕ) {W D W' : ℕ} (hW : W * D = W') : Fin (m * n * W * D) ≃ Fin (m * n * W') :=
  finCongr (by rw [← hW, Nat.mul_assoc])

/-- The multi-round adversary `A` with every unitary, every round and the final
projector tensored with `1` on the ancilla `Fin D`, and the initial state
`ρ ⊗ |0⟩⟨0|`. -/
def liftMR [NeZero D] (e : Fin (m * n * W * D) ≃ Fin (m * n * W'))
    (A : QAdvMR m n W q k c a) : QAdvMR m n W' q k c a where
  seg j i := liftU e (A.seg j i)
  rounds j := liftRA e (A.rounds j)
  init :=
    { val := kr e A.init.val (ancProj 0)
      psd := kr_posSemidef _ A.init.psd (ancProj_posSemidef 0)
      tr_one := by rw [trace_kr, A.init.tr_one, trace_ancProj, one_mul] }
  final := kr e A.final 1
  final_conjTranspose := by rw [kr_conjTranspose, A.final_conjTranspose, conjTranspose_one]
  final_mul_self := by rw [kr_mul, A.final_mul_self, one_mul]

/-- The final measurement of the lifted adversary lifts the final measurement. -/
theorem liftsQ_measure [NeZero D] (e : Fin (m * n * W * D) ≃ Fin (m * n * W'))
    (A : QAdvMR m n W q k c a) : LiftsQ e A.measure (liftMR e A).measure := by
  intro b B E
  rw [QAdvMR.measure, QAdvMR.measure]
  cases b
  · rw [measProj_branch_false, measProj_branch_false]
    show (1 - kr e A.final 1) * kr e B E * (1 - kr e A.final 1)ᴴ =
      kr e ((1 - A.final) * B * (1 - A.final)ᴴ) E
    rw [kr_one_sub, kr_conjTranspose, kr_mul, kr_mul, conjTranspose_one, one_mul, mul_one]
  · rw [measProj_branch_true, measProj_branch_true]
    show kr e A.final 1 * kr e B E * (kr e A.final 1)ᴴ = kr e (A.final * B * A.finalᴴ) E
    rw [kr_conjTranspose, kr_mul, kr_mul, conjTranspose_one, one_mul, mul_one]

/-- The lifted adversary outputs `1` with the probability of `A`. -/
theorem prOutMR_liftMR [NeZero n] [NeZero D] (hW : W * D = W') (A : QAdvMR m n W q k c a)
    (H : Fin m → Fin n) (f : Fin c → Fin a) :
    prOutMR (liftMR (padE m n hW) A) H f = prOutMR A H f := by
  subst hW
  have hOU : oracleU m n (W * D) H = liftU (ancE m n W D) (oracleU m n W H) :=
    Subtype.ext (oracleU_lift H)
  have hO : LiftsQ (ancE m n W D)
      (QComp.qbind (oracleQ m n W H) fun _ => QComp.qpure false)
      (QComp.qbind (oracleQ m n (W * D) H) fun _ => QComp.qpure false) := by
    refine liftsQ_qbind _ ?_ fun _ => liftsQ_qpure _ false
    rw [oracleQ, oracleQ, hOU]
    exact liftsQ_unitaryChannel _ _
  have hrun : ∀ {W₁ : ℕ} (B : QAdvMR m n W₁ q k c a), runMR B H f =
      QComp.qbind (mrChainSC (QComp.qbind (oracleQ m n W₁ H) fun _ => QComp.qpure false) f k q
        (B.seg 0) (Fin.tail B.seg) B.rounds) fun _ => B.measure := by
    intro W₁ B
    rw [mrChainSC_qbind_pure_false, QComp.qbind_assoc]
    simp only [QComp.qpure_qbind]
    rfl
  have hL : LiftsQ (ancE m n W D) (runMR A H f) (runMR (liftMR (padE m n rfl) A) H f) := by
    rw [hrun, hrun]
    exact liftsQ_qbind _
      (liftsQ_mrChainSC_liftRA _ _ _ hO f k q (A.seg 0) (Fin.tail A.seg) A.rounds)
      fun _ => liftsQ_measure _ A
  unfold prOutMR prTrue_Q
  show ENNReal.ofReal (((runMR (liftMR (padE m n rfl) A) H f).branch true
      (kr (ancE m n W D) A.init.val (ancProj 0))).trace.re) = _
  rw [hL, trace_kr, trace_ancProj, mul_one]

/-- A cast of the work register moves into the index equivalence. -/
theorem castMR_liftMR [NeZero D] {W₂ : ℕ} (hW : W * D = W') (h : W' = W₂)
    (A : QAdvMR m n W q k c a) :
    castMR h (liftMR (padE m n hW) A) = liftMR (padE m n (hW.trans h)) A := by
  subst h
  rfl

end Lift

/-! ## The output projector on the padded register -/

section WinBit

/-- `1 ⊗ (X ⊗ 1_{w D})` is the lift of `1 ⊗ (X ⊗ 1_w)` along the associativity
cast. -/
theorem one_kron_kron_one_lift {p r w D : ℕ} (X : Matrix (Fin r) (Fin r) ℂ)
    (e : Fin (p * (r * w) * D) ≃ Fin (p * (r * (w * D)))) (he : ∀ i, (e i : ℕ) = i) :
    (1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ (X ⊗ₖ (1 : Matrix (Fin (w * D)) (Fin (w * D)) ℂ)) =
      kr e ((1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ (X ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ))) 1 := by
  have key : ∀ (a : Fin p) (b : Fin r) (x : Fin w) (y : Fin D),
      e.symm (finProdEquiv p (r * (w * D)) (a, finProdEquiv r (w * D) (b, finProdEquiv w D (x, y))))
        = finProdEquiv (p * (r * w)) D
          (finProdEquiv p (r * w) (a, finProdEquiv r w (b, x)), y) := by
    intro a b x y
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    rw [he]
    simp only [finProdEquiv, finProdFinEquiv_apply_val]
    ring
  ext i j
  obtain ⟨⟨a, i'⟩, rfl⟩ := (finProdEquiv p (r * (w * D))).surjective i
  obtain ⟨⟨b, i''⟩, rfl⟩ := (finProdEquiv r (w * D)).surjective i'
  obtain ⟨⟨x, y⟩, rfl⟩ := (finProdEquiv w D).surjective i''
  obtain ⟨⟨a', j'⟩, rfl⟩ := (finProdEquiv p (r * (w * D))).surjective j
  obtain ⟨⟨b', j''⟩, rfl⟩ := (finProdEquiv r (w * D)).surjective j'
  obtain ⟨⟨x', y'⟩, rfl⟩ := (finProdEquiv w D).surjective j''
  simp only [kr, Matrix.submatrix_apply, key, kronecker_apply, Equiv.symm_apply_apply,
    Matrix.one_apply, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hx : x = x' <;> by_cases hy : y = y' <;> simp [hx, hy]

/-- The output projector on the work register `w * D` is the lift of the output
projector on the work register `w`. -/
theorem winBitProj_pad (M n w D : ℕ) (hW : 2 * w * D = 2 * (w * D)) :
    winBitProj M n (w * D) = kr (padE M n hW) (winBitProj M n w) 1 := by
  unfold winBitProj
  exact one_kron_kron_one_lift _ _ fun _ => rfl

end WinBit

/-! ## The clean projector as a projector on the ancilla -/

section Clean

variable (m n w c : ℕ) [NeZero m] [NeZero n] [NeZero c]

instance instNeZeroAncDim : NeZero (ancDim m n c) := by
  unfold ancDim; infer_instance

/-- The projector onto the ancilla states whose two parked slots are `0`. -/
def ancCleanProj : Matrix (Fin (ancDim m n c)) (Fin (ancDim m n c)) ℂ :=
  Matrix.diagonal fun t => if ((ancIndex m n c).symm t).2 = ((0, 0), (0, 0)) then 1 else 0

/-- The zero index of the ancilla has record slot and parked slots `0`. -/
theorem ancIndex_symm_zero : (ancIndex m n c).symm 0 = (0, (0, 0), (0, 0)) := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  show ((0 : Fin (ancDim m n c)) : ℕ) = ((finProdEquiv (c * (m * n)) (m * n))
    (finProdEquiv c (m * n) (0, finProdEquiv m n (0, 0)), finProdEquiv m n (0, 0)) : ℕ)
  simp [finProdEquiv, finProdFinEquiv_apply_val]

set_option linter.unusedSectionVars false in
/-- The row-major index of the query and work registers followed by the
ancilla is the index `roundIndex` of the round register. -/
theorem ancE_eq_roundIndex (s : Fin m × Fin n) (z : Fin w) (t : Fin (ancDim m n c)) :
    ancE m n w (ancDim m n c) (finProdEquiv (m * n * w) (ancDim m n c) (oracleIndex m n w (s, z), t))
      = roundIndex m n w c (s, z, (ancIndex m n c).symm t) := by
  apply Fin.ext
  simp only [ancE, finCongr_apply, Fin.val_cast, roundIndex_apply, oracleIndex, ancFlat,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id,
    Equiv.apply_symm_apply, finProdEquiv, finProdFinEquiv_apply_val]
  ring

/-- `cleanProjM` is `1 ⊗ ancCleanProj` along `ancE`. -/
theorem cleanProjM_eq_kr :
    cleanProjM m n w c = kr (ancE m n w (ancDim m n c)) 1 (ancCleanProj m n c) := by
  have hdec : ∀ i : Fin (m * n * (w * ancDim m n c)), ∃ s z t,
      i = roundIndex m n w c (s, z, (ancIndex m n c).symm t) ∧
      (ancE m n w (ancDim m n c)).symm i =
        finProdEquiv (m * n * w) (ancDim m n c) (oracleIndex m n w (s, z), t) := by
    intro i
    obtain ⟨⟨u, t⟩, hu⟩ := (finProdEquiv (m * n * w) (ancDim m n c)).surjective
      ((ancE m n w (ancDim m n c)).symm i)
    obtain ⟨⟨s, z⟩, rfl⟩ := (oracleIndex m n w).surjective u
    refine ⟨s, z, t, ?_, hu.symm⟩
    rw [← ancE_eq_roundIndex, hu, Equiv.apply_symm_apply]
  ext i j
  obtain ⟨s, z, t, rfl, hi⟩ := hdec i
  obtain ⟨s', z', t', rfl, hj⟩ := hdec j
  simp only [kr, Matrix.submatrix_apply, hi, hj, TensorProduct.kronecker_apply,
    Equiv.symm_apply_apply, cleanProjM, ancCleanProj, Matrix.diagonal_apply, Matrix.one_apply,
    IsClean,
    Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq]
  by_cases hs : s = s' <;> by_cases hz : z = z' <;> by_cases ht : t = t' <;>
    simp [hs, hz, ht]

/-- `ancCleanProj` fixes the ancilla state `|0⟩⟨0|`. -/
theorem ancCleanProj_ancProj_zero :
    ancCleanProj m n c * ancProj 0 * ancCleanProj m n c = ancProj 0 := by
  rw [ancCleanProj, ancProj, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext t
  by_cases ht : t = 0
  · subst ht
    simp [ancIndex_symm_zero]
  · simp [ht]

end Clean

/-! ## The padded KEM adversary -/

section Pad

variable {m₁ m₂ n w q k c a : ℕ} {PK C K : Type} [NeZero (m₁ + m₂)] [NeZero n] [NeZero c]

/-- The KEM adversary `A` on the work register `w * ancDim (m₁ + m₂) n c`: every
unitary, round and the final projector tensored with `1` on the ancilla, and
the initial state tensored with `|0⟩⟨0|`. -/
def padAdv (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    KEMQAdv m₁ m₂ n (w * ancDim (m₁ + m₂) n c) q k c a PK C K where
  run pk cs κ :=
    liftMR (padE (m₁ + m₂) n (Nat.mul_assoc 2 w (ancDim (m₁ + m₂) n c))) (A.run pk cs κ)
  final_eq pk cs κ := by
    show kr _ (A.run pk cs κ).final 1 = _
    rw [A.final_eq, winBitProj_pad]
  pure pk cs κ := by
    obtain ⟨ψ, hψ⟩ := A.pure pk cs κ
    exact ⟨_, show kr _ (A.run pk cs κ).init.val (ancProj 0) = _ by
      rw [hψ, ancProj_zero_eq_vecMulVec, kr_vecMulVec]⟩

variable {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [Fintype Z] [Fintype K] [Nonempty K] [DecidableEq C] (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

/-- Padding leaves the winning probability unchanged. -/
theorem prWinKEM_padAdv (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinKEM P hpk eG eJ eKR eC eKa (padAdv A) b = prWinKEM P hpk eG eJ eKR eC eKa A b := by
  unfold prWinKEM
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [padAdv, prOutMR_liftMR]

/-- Padding leaves the IND-CCA advantage unchanged. -/
theorem qINDCCAAdvantage_padAdv (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    qINDCCAAdvantage P hpk eG eJ eKR eC eKa (padAdv A) =
      qINDCCAAdvantage P hpk eG eJ eKR eC eKa A := by
  rw [qINDCCAAdvantage, qINDCCAAdvantage, prWinKEM_padAdv, prWinKEM_padAdv]

end Pad

/-! ## The segment and initial-state hypotheses for the padded adversary -/

section PadHyp

variable {m₁ m₂ n w q k c a : ℕ} {PK C K : Type} [NeZero (m₁ + m₂)] [NeZero n] [NeZero c]

/-- The padded adversary on the work register `(2 * w) * ancDim …`. -/
theorem castMR_padAdv (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (pk : PK) (cs : C) (κ : K) :
    castMR (Nat.mul_assoc 2 w (ancDim (m₁ + m₂) n c)).symm ((padAdv A).run pk cs κ) =
      liftMR (ancE (m₁ + m₂) n (2 * w) (ancDim (m₁ + m₂) n c)) (A.run pk cs κ) :=
  castMR_liftMR _ _ _

/-- The segment unitaries of the padded adversary commute with `cleanProjM`. -/
theorem padAdv_hseg (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (pk : PK) (cs : C) (κ : K)
    (j : Fin (k + 1)) (i : Fin (q + 1)) :
    ((castMR (Nat.mul_assoc 2 w (ancDim (m₁ + m₂) n c)).symm ((padAdv A).run pk cs κ)).seg j i :
        Matrix _ _ ℂ) * cleanProjM (m₁ + m₂) n (2 * w) c =
      cleanProjM (m₁ + m₂) n (2 * w) c *
        ((castMR (Nat.mul_assoc 2 w (ancDim (m₁ + m₂) n c)).symm ((padAdv A).run pk cs κ)).seg j i :
          Matrix _ _ ℂ) := by
  rw [castMR_padAdv, cleanProjM_eq_kr]
  show kr _ _ 1 * kr _ 1 _ = kr _ 1 _ * kr _ _ 1
  rw [kr_mul, kr_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]

/-- The initial state of the padded adversary is supported on the clean slice. -/
theorem padAdv_hinit (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (pk : PK) (cs : C) (κ : K) :
    SupportedOn (cleanProjM (m₁ + m₂) n (2 * w) c)
      (castMR (Nat.mul_assoc 2 w (ancDim (m₁ + m₂) n c)).symm ((padAdv A).run pk cs κ)).init.val := by
  rw [castMR_padAdv, cleanProjM_eq_kr, SupportedOn]
  show kr _ 1 _ * kr _ _ (ancProj 0) * kr _ 1 _ = kr _ _ (ancProj 0)
  rw [kr_mul, kr_mul, Matrix.one_mul, Matrix.mul_one, ancCleanProj_ancProj_zero]

end PadHyp

/-! ## One classical round as a basis measurement with a shift answer -/

section OneRound

variable {d c a d' : ℕ}

theorem ancUnit_self (y : Fin c) : ancUnit y y = ancProj y := by
  ext i j
  by_cases hi : i = y <;> by_cases hj : j = y
  · subst hi hj; simp [ancUnit, ancProj]
  · subst hi; simp [ancUnit, ancProj, hj, Ne.symm hj]
  · subst hj; simp [ancUnit, ancProj, hi]
  · simp [ancUnit, ancProj, Matrix.diagonal_apply, hi]

/-- Conjugating a block `B ⊗ |y⟩⟨y'|` by `A ⊗ |z⟩⟨z|` keeps it only at
`y = y' = z`. -/
theorem kr_ancProj_conj_kr_ancUnit (e : Fin (d * c) ≃ Fin d') (A B : Matrix (Fin d) (Fin d) ℂ)
    (z y y' : Fin c) :
    kr e A (ancProj z) * kr e B (ancUnit y y') * (kr e A (ancProj z))ᴴ =
      if z = y ∧ z = y' then kr e (A * B * Aᴴ) (ancProj z) else 0 := by
  rw [kr_conjTranspose, kr_mul, kr_mul, ancProj_conjTranspose, ancProj_mul_ancUnit]
  by_cases hy : z = y
  · subst hy
    rw [if_pos rfl, ancUnit_mul_ancProj]
    by_cases hy' : z = y'
    · subst hy'
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, ancUnit_self]
    · rw [if_neg hy', if_neg fun h => hy' h.2, kr_zero_right]
  · rw [if_neg hy, if_neg fun h => hy h.1, zero_mul, kr_zero_right]

/-- `tr ((X ⊗ 1) ∑ y, B y ⊗ |g y⟩⟨g y|) = ∑ y, tr (X B y)`. -/
theorem trace_kr_one_mul_sum_ancProj {ι : Type} [Fintype ι] (e : Fin (d * c) ≃ Fin d')
    (X : Matrix (Fin d) (Fin d) ℂ) (B : ι → Matrix (Fin d) (Fin d) ℂ) (g : ι → Fin c) :
    (kr e X 1 * ∑ y, kr e (B y) (ancProj (g y))).trace = ∑ y, (X * B y).trace := by
  rw [Finset.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [kr_mul, one_mul, trace_kr, trace_ancProj, mul_one]

/-- The round measuring a record ancilla `Fin c` in the computational basis and
answering by the answer unitaries of `R` on the register. -/
def recRound (e : Fin (d * c) ≃ Fin d') (R : ClassicalRound d c a) : ClassicalRound d' c a where
  P y := kr e 1 (ancProj y)
  P_conjTranspose y := by rw [kr_conjTranspose, conjTranspose_one, ancProj_conjTranspose]
  P_mul_self y := by rw [kr_mul, one_mul, ancProj_mul_ancProj, if_pos rfl]
  P_orth y y' h := by rw [kr_mul, ancProj_mul_ancProj, if_neg h, kr_zero_right]
  P_sum := by rw [← kr_sum_right, sum_ancProj, kr_one]
  ans k := liftU e (R.ans k)

/-- Copying the outcome of `R` into the record by `roundW` and measuring the
record in the computational basis leaves the outcome-`y` branch of `R` next to
`|y⟩⟨y|`. -/
theorem roundU_recRound_roundW [NeZero c] (e : Fin (d * c) ≃ Fin d') (R : ClassicalRound d c a)
    (f : Fin c → Fin a) (σ : Matrix (Fin d) (Fin d) ℂ) :
    (roundU (recRound e R) f).branch () (roundW e R * kr e σ (ancProj 0) * (roundW e R)ᴴ) =
      ∑ y, kr e (((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y) * σ *
        ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y)ᴴ) (ancProj y) := by
  rw [roundU_branch, roundW_mul_kr_mul_conjTranspose]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hop : ((recRound e R).ans (f z) : Matrix (Fin d') (Fin d') ℂ) * (recRound e R).P z =
      kr e (R.ans (f z) : Matrix (Fin d) (Fin d) ℂ) (ancProj z) := by
    show kr e _ 1 * kr e 1 (ancProj z) = _
    rw [kr_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hop, Finset.mul_sum, Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.sum_mul, kr_ancProj_conj_kr_ancUnit]
  rw [Finset.sum_eq_single z, Finset.sum_eq_single z]
  · rw [if_pos ⟨rfl, rfl⟩, conjTranspose_mul, R.P_conjTranspose]
    simp only [Matrix.mul_assoc]
  · intro y' _ hy'
    rw [if_neg fun h => hy' h.2.symm]
  · intro h; exact absurd (Finset.mem_univ z) h
  · intro y _ hy
    exact Finset.sum_eq_zero fun y' _ => if_neg fun h => hy h.1.symm
  · intro h; exact absurd (Finset.mem_univ z) h

/-- Seen through `X ⊗ 1`, the copy by `roundW` followed by `recRound` is the
round `R`. -/
theorem trace_recRound_roundW [NeZero c] (e : Fin (d * c) ≃ Fin d') (R : ClassicalRound d c a)
    (f : Fin c → Fin a) (X σ : Matrix (Fin d) (Fin d) ℂ) :
    (kr e X 1 * (roundU (recRound e R) f).branch ()
        (roundW e R * kr e σ (ancProj 0) * (roundW e R)ᴴ)).trace =
      (X * (roundU R f).branch () σ).trace := by
  rw [roundU_recRound_roundW, trace_kr_one_mul_sum_ancProj, roundU_branch, Finset.mul_sum,
    trace_sum]

/-- The round measuring with the projectors of `R` tensored with `1` on an
answer register `Fin a`, and answering `k` by the cyclic shift `|j⟩ ↦ |j + k⟩` of
that register. -/
def xorRound [NeZero a] (e : Fin (d * a) ≃ Fin d') (R : ClassicalRound d c a) :
    ClassicalRound d' c a :=
  { liftRA e R with
    ans := fun k => ⟨kr e 1 (ancShift k), kr_mem_unitaryGroup e (one_mem _)
      (Matrix.mem_unitaryGroup_iff.mpr (by
        rw [star_eq_conjTranspose]; exact ancShift_mul_conjTranspose_self k))⟩ }

/-- The answer unitaries of `R` controlled on the answer register:
`∑ k, ans k ⊗ |k⟩⟨k|`. -/
def ctrlAns (e : Fin (d * a) ≃ Fin d') (R : ClassicalRound d c a) : Matrix (Fin d') (Fin d') ℂ :=
  ∑ k, kr e (R.ans k : Matrix (Fin d) (Fin d) ℂ) (ancProj k)

theorem ctrlAns_mul_conjTranspose_self (e : Fin (d * a) ≃ Fin d') (R : ClassicalRound d c a) :
    ctrlAns e R * (ctrlAns e R)ᴴ = 1 := by
  unfold ctrlAns
  rw [conjTranspose_sum, Finset.sum_mul_sum]
  simp only [kr_conjTranspose, kr_mul, ancProj_conjTranspose, ancProj_mul_ancProj]
  have h : ∀ k, ∑ k', kr e ((R.ans k : Matrix (Fin d) (Fin d) ℂ) *
      (R.ans k' : Matrix (Fin d) (Fin d) ℂ)ᴴ) (if k = k' then ancProj k else 0) =
      kr e 1 (ancProj k) := by
    intro k
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, ← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp (R.ans k).prop]
    · intro k' _ hk'; rw [if_neg (Ne.symm hk'), kr_zero_right]
    · intro h; exact absurd (Finset.mem_univ k) h
  simp only [h, ← kr_sum_right, sum_ancProj, kr_one]

/-- The shift answer on the answer register at `|0⟩`, followed by the controlled
answer `ctrlAns`, leaves the outcome-`y` branch of `R` next to `|f y⟩⟨f y|`. -/
theorem ctrlAns_roundU_xorRound [NeZero a] (e : Fin (d * a) ≃ Fin d')
    (R : ClassicalRound d c a) (f : Fin c → Fin a) (σ : Matrix (Fin d) (Fin d) ℂ) :
    ctrlAns e R * (roundU (xorRound e R) f).branch () (kr e σ (ancProj 0)) * (ctrlAns e R)ᴴ =
      ∑ y, kr e (((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y) * σ *
        ((R.ans (f y) : Matrix (Fin d) (Fin d) ℂ) * R.P y)ᴴ) (ancProj (f y)) := by
  have hround : (roundU (xorRound e R) f).branch () (kr e σ (ancProj 0)) =
      ∑ y, kr e (R.P y * σ * R.P y) (ancProj (f y)) := by
    rw [roundU_branch]
    refine Finset.sum_congr rfl fun y _ => ?_
    show kr e 1 (ancShift (f y)) * kr e (R.P y) 1 * kr e σ (ancProj 0) *
      (kr e 1 (ancShift (f y)) * kr e (R.P y) 1)ᴴ = _
    rw [kr_mul, kr_conjTranspose, kr_mul, kr_mul]
    simp only [Matrix.one_mul, Matrix.mul_one, R.P_conjTranspose]
    rw [ancShift_mul_ancProj_zero_mul_conjTranspose, ancUnit_self]
  rw [hround, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  unfold ctrlAns
  rw [conjTranspose_sum, Finset.sum_mul, Finset.sum_mul_sum]
  simp only [← ancUnit_self (f y), kr_conjTranspose, kr_mul, ancProj_conjTranspose,
    ancProj_mul_ancUnit, ite_mul, zero_mul, ancUnit_mul_ancProj]
  rw [Finset.sum_eq_single (f y), Finset.sum_eq_single (f y)]
  · simp only [if_true, ancUnit_self, conjTranspose_mul, R.P_conjTranspose, Matrix.mul_assoc]
  · intro k' _ hk'; simp [hk', kr_zero_right]
  · intro h; exact absurd (Finset.mem_univ (f y)) h
  · intro k _ hk
    refine Finset.sum_eq_zero fun k' _ => ?_
    simp [hk, kr_zero_right]
  · intro h; exact absurd (Finset.mem_univ (f y)) h

/-- Seen through `X ⊗ 1`, the shift answer followed by `ctrlAns` is the round
`R`. -/
theorem trace_ctrlAns_xorRound [NeZero a] (e : Fin (d * a) ≃ Fin d')
    (R : ClassicalRound d c a) (f : Fin c → Fin a) (X σ : Matrix (Fin d) (Fin d) ℂ) :
    (kr e X 1 * (ctrlAns e R * (roundU (xorRound e R) f).branch () (kr e σ (ancProj 0)) *
        (ctrlAns e R)ᴴ)).trace = (X * (roundU R f).branch () σ).trace := by
  rw [ctrlAns_roundU_xorRound, trace_kr_one_mul_sum_ancProj, roundU_branch, Finset.mul_sum,
    trace_sum]

/-- **One classical round in normal form.** On the register extended by a
record `Fin c` (along `e₁`) and an answer register `Fin a` (along `e₂`): copy the
outcome of `R` into the record by `roundW`, measure the record in the
computational basis and answer `f y` by the shift of the answer register
(`xorRound e₂ (recRound e₁ R)`), then apply the answers of `R` controlled on the
answer register. Seen through `X ⊗ 1 ⊗ 1`, this is the round `R`. -/
theorem trace_normalForm_round [NeZero c] [NeZero a] {d'' : ℕ} (e₁ : Fin (d * c) ≃ Fin d')
    (e₂ : Fin (d' * a) ≃ Fin d'') (R : ClassicalRound d c a) (f : Fin c → Fin a)
    (X σ : Matrix (Fin d) (Fin d) ℂ) :
    (kr e₂ (kr e₁ X 1) 1 *
      (ctrlAns e₂ (recRound e₁ R) * (roundU (xorRound e₂ (recRound e₁ R)) f).branch ()
        (kr e₂ (roundW e₁ R * kr e₁ σ (ancProj 0) * (roundW e₁ R)ᴴ) (ancProj 0)) *
        (ctrlAns e₂ (recRound e₁ R))ᴴ)).trace =
      (X * (roundU R f).branch () σ).trace := by
  rw [trace_ctrlAns_xorRound, trace_recRound_roundW]

/-- The projectors of the normal-form round measure the record in the
computational basis. -/
theorem xorRound_recRound_P [NeZero a] {d'' : ℕ} (e₁ : Fin (d * c) ≃ Fin d')
    (e₂ : Fin (d' * a) ≃ Fin d'') (R : ClassicalRound d c a) (y : Fin c) :
    (xorRound e₂ (recRound e₁ R)).P y = kr e₂ (kr e₁ 1 (ancProj y)) 1 := rfl

/-- The answers of the normal-form round are shifts of the answer register. -/
theorem xorRound_ans [NeZero a] (e : Fin (d * a) ≃ Fin d') (R : ClassicalRound d c a)
    (k : Fin a) : ((xorRound e R).ans k : Matrix (Fin d') (Fin d') ℂ) = kr e 1 (ancShift k) := rfl

end OneRound

end CatCrypt.Quantum.QROM

end

end
