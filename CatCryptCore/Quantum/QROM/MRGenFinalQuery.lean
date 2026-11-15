/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.RecordRounds
public import CatCryptCore.Quantum.QROM.RoundsViaOracle

/-!
# A final test that reads the oracle, as one more query of a multi-round adversary

A diagonal final test `g i (H (p i))` of a general multi-round adversary
`B : QAdvMRGen m n w q k c a` reads the oracle `H` at the point `p i` of the final basis
state `i`. The adversary `B.withFinalQuery p g : QAdvMRGen m n (w * (m * n)) (q + 1) k c a`
computes this value with one more query after the last local operation of its last segment,
as `finalQAdv` does for a single-run adversary: the permutation unitary of `finalPerm p` moves
the query register into an ancilla `Fin m × Fin n` started at `(0, 0)` and writes `p i` into
the query register, the query writes `H (p i)` into the value register, and the final
projector is the diagonal projector of `finalAcc g`, which does not depend on `H`. Every
segment of a `QAdvMRGen` has the same number of queries, so each of the other `k` segments
starts with the dummy query of `RoundsViaOracle` (the gadget of the trivial round `trivR`),
which leaves the ancilla at `(0, 0)`. The flattened query count is `flatQ q k q + (k + 1)`
(`flatQ_succ_succ`).

For the flattened adversary of a multi-round adversary `A : QAdvMR m n w q k c a` with the
round function `f`, the diagonal test that reads the oracle is the final query of the recorded
adversary `recordGen A`, at every oracle and round function
(`prOut_withFinalB_toQAdv_eq_prOutMRGen_finalQuery`).

## Main definitions

* `FinalRelQ e O O'` — `O'` on `B ⊗ |0⟩⟨0|` accepts with the trace with which `O` accepts on `B`
* `finalOps U X Y` — the operations `U 0, …, U q` with `X` after `U q`, and `Y` after one more
  query
* `QAdvMRGen.withFinalQuery B p g` — the adversary with the final query

## Main results

* `chainG_snoc`, `chainG_snoc_init` — a chain with one more operation at its end
* `finalRelQ_mrChainG` — the chains of two adversaries whose segments other than the last
  preserve the ancilla and whose last segments with the final measurements are related by
  `FinalRelQ`
* `prOutMRGen_withFinalQuery_eq` — the acceptance probability of the final query is the one of
  the test that reads the oracle
* `prOut_withFinalB_toQAdv_eq_prOutMRGen_finalQuery`, `exists_prOutMRGen_finalQuery` — the same
  for the flattened adversary of a multi-round adversary
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.UnitaryChannel

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Chains with one more operation at the end -/

section Snoc

variable {d : ℕ}

/-- A chain with one more operation `Y` after one more query. -/
theorem chainG_snoc (O : QComp d Unit) :
    ∀ (q : ℕ) (W : Fin (q + 1) → QComp d Unit) (Y : QComp d Unit),
      chainG O (q + 1) (Fin.snoc W Y) =
        QComp.qbind (chainG O q W) fun _ => QComp.qbind O fun _ => Y
  | 0, W, Y => by
    simp only [chainG]
    rfl
  | q + 1, W, Y => by
    have ht : Fin.tail (Fin.snoc W Y : Fin (q + 1 + 1 + 1) → QComp d Unit) =
        Fin.snoc (Fin.tail W) Y := by
      conv_lhs => rw [← Fin.cons_self_tail W]
      rw [← Fin.cons_snoc_eq_snoc_cons, Fin.tail_cons]
    rw [chainG, ht, chainG_snoc O q (Fin.tail W) Y]
    conv_rhs => rw [chainG]
    simp only [QComp.qbind_assoc]
    rfl

/-- A chain whose last operation is followed by `X`. -/
theorem chainG_snoc_init (O : QComp d Unit) :
    ∀ (q : ℕ) (W : Fin (q + 1) → QComp d Unit) (X : QComp d Unit),
      chainG O q (Fin.snoc (Fin.init W) (QComp.qbind (W (Fin.last q)) fun _ => X)) =
        QComp.qbind (chainG O q W) fun _ => X
  | 0, W, X => by
    simp only [chainG]
    rfl
  | q + 1, W, X => by
    have ht : Fin.tail (Fin.snoc (Fin.init W) (QComp.qbind (W (Fin.last (q + 1))) fun _ => X) :
        Fin (q + 1 + 1) → QComp d Unit) =
        Fin.snoc (Fin.init (Fin.tail W)) (QComp.qbind (Fin.tail W (Fin.last q)) fun _ => X) := by
      conv_lhs => rw [← Fin.cons_self_tail (Fin.init W)]
      rw [← Fin.cons_snoc_eq_snoc_cons, Fin.tail_cons, Fin.tail_init_eq_init_tail]
      rfl
    rw [chainG, ht, chainG_snoc_init O q (Fin.tail W) X]
    conv_rhs => rw [chainG]
    simp only [QComp.qbind_assoc]
    rfl

end Snoc

/-! ## The acceptance relation of the final segment -/

section FinalRel

variable {d c D : ℕ} [NeZero c]

/-- `O'` accepts on `B ⊗ |0⟩⟨0|` with the trace with which `O` accepts on `B`. -/
def FinalRelQ (e : Fin (d * c) ≃ Fin D) (O : QComp d Bool) (O' : QComp D Bool) : Prop :=
  ∀ B : Matrix (Fin d) (Fin d) ℂ, ((O'.branch true (kr e B (ancProj 0))).trace =
    (O.branch true B).trace)

/-- A step that preserves the ancilla followed by related continuations is related. -/
theorem finalRelQ_qbind {e : Fin (d * c) ≃ Fin D} {I : QComp d Unit} {I' : QComp D Unit}
    {g : Unit → QComp d Bool} {g' : Unit → QComp D Bool} (hI : PresAncQ e I I')
    (hg : FinalRelQ e (g ()) (g' ())) :
    FinalRelQ e (QComp.qbind I g) (QComp.qbind I' g') := fun B => by
  rw [qbind_unit_branch, qbind_unit_branch, hI, hg]

/-- The chains of two multi-round adversaries: if every segment but the last preserves the
    ancilla and the last segments followed by the final measurements are related by
    `FinalRelQ`, the whole runs are. -/
theorem finalRelQ_mrChainG (e : Fin (d * c) ≃ Fin D) {c' a' q : ℕ} (O : QComp d Unit)
    (O' : QComp D Unit) (f : Fin c' → Fin a') (M : QComp d Bool) (M' : QComp D Bool) :
    ∀ (k : ℕ) (segs : Fin (k + 1) → Fin (q + 1) → QComp d Unit)
      (segs' : Fin (k + 1) → Fin (q + 1 + 1) → QComp D Unit)
      (R : Fin k → ClassicalRound d c' a') (R' : Fin k → ClassicalRound D c' a'),
      (∀ j : Fin k, PresAncQ e (chainG O q (segs j.castSucc))
        (chainG O' (q + 1) (segs' j.castSucc))) →
      FinalRelQ e (QComp.qbind (chainG O q (segs (Fin.last k))) fun _ => M)
        (QComp.qbind (chainG O' (q + 1) (segs' (Fin.last k))) fun _ => M') →
      (∀ j, LiftsQ e (roundU (R j) f) (roundU (R' j) f)) →
      FinalRelQ e (QComp.qbind (mrChainG O f k q (segs 0) (Fin.tail segs) R) fun _ => M)
        (QComp.qbind (mrChainG O' f k (q + 1) (segs' 0) (Fin.tail segs') R') fun _ => M')
  | 0, segs, segs', _, _, _, hF, _ => hF
  | k + 1, segs, segs', R, R', hD, hF, hR => by
    simp only [mrChainG, QComp.qbind_assoc]
    refine finalRelQ_qbind (hD 0) (finalRelQ_qbind (hR 0).presAncQ ?_)
    exact finalRelQ_mrChainG e O O' f M M' k (Fin.tail segs) (Fin.tail segs') (Fin.tail R)
      (Fin.tail R') (fun j => hD j.succ) hF (fun j => hR j.succ)

end FinalRel

/-! ## The segment with the final query -/

section FinalOps

variable {D q : ℕ}

/-- The operations `U 0, …, U q` with `X` after `U q`, followed by `Y`; in a chain one more
    query comes between `X` and `Y`. -/
def finalOps (U : Fin (q + 1) → CPComp D Unit) (X Y : CPComp D Unit) :
    Fin (q + 1 + 1) → CPComp D Unit :=
  Fin.snoc (Fin.snoc (Fin.init U) (compCh (U (Fin.last q)) X)) Y

/-- The operations of `finalOps` are trace preserving. -/
theorem isTP_finalOps (U : Fin (q + 1) → CPComp D Unit)
    (hU : ∀ i, IsTP ((U i).toQComp.branch ())) (X Y : CPComp D Unit)
    (hX : IsTP (X.toQComp.branch ())) (hY : IsTP (Y.toQComp.branch ())) (i : Fin (q + 1 + 1)) :
    IsTP ((finalOps U X Y i).toQComp.branch ()) := by
  induction i using Fin.lastCases with
  | last => rw [finalOps, Fin.snoc_last]; exact hY
  | cast i =>
    rw [finalOps, Fin.snoc_castSucc]
    induction i using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact isTP_compCh (hU _) hX
    | cast i => rw [Fin.snoc_castSucc]; exact hU _

/-- The chain of `finalOps U X Y`: the chain of `U`, then `X`, one more query and `Y`. -/
theorem chainG_finalOps (O : QComp D Unit) (U : Fin (q + 1) → CPComp D Unit)
    (X Y : CPComp D Unit) :
    chainG O (q + 1) (fun i => (finalOps U X Y i).toQComp) =
      QComp.qbind (chainG O q fun i => (U i).toQComp) fun _ =>
        QComp.qbind X.toQComp fun _ => QComp.qbind O fun _ => Y.toQComp := by
  have h : (fun i => (finalOps U X Y i).toQComp) =
      Fin.snoc (Fin.snoc (Fin.init fun i => (U i).toQComp)
        (QComp.qbind (U (Fin.last q)).toQComp fun _ => X.toQComp)) Y.toQComp := by
    change CPComp.toQComp ∘ finalOps U X Y = _
    rw [finalOps, Fin.comp_snoc, Fin.comp_snoc, Fin.comp_init, compCh, CPComp.toQComp_qbind]
    rfl
  rw [h, chainG_snoc, chainG_snoc_init, QComp.qbind_assoc]

end FinalOps

/-! ## The final query -/

section Final

variable {m n w q k c a : ℕ} [NeZero m] [NeZero n]

/-- `B` with the final projector `diagB G`. -/
def QAdvMRGen.withFinalB (B : QAdvMRGen m n w q k c a) (G : Fin (m * n * w) → Bool) :
    QAdvMRGen m n w q k c a where
  seg := B.seg
  seg_tp := B.seg_tp
  rounds := B.rounds
  init := B.init
  final := diagB G
  final_conjTranspose := diagB_conjTranspose G
  final_mul_self := diagB_mul_self G

/-- After the permutation of `finalPerm p` and one more query, the projector of `finalAcc g`
    on `B ⊗ |0⟩⟨0|` accepts with the trace with which the test `g i (H (p i))` accepts on
    `B`. -/
theorem finalRelQ_finalStep (p : Fin (m * n * w) → Fin m) (g : Fin (m * n * w) → Fin n → Bool)
    (H : Fin m → Fin n) :
    FinalRelQ (ancE m n w (m * n))
      (measProj (diagB fun i => g i (H (p i))) (diagB_conjTranspose _) (diagB_mul_self _))
      (QComp.qbind (CPComp.unitary (permUnitary (finalPerm p))).toQComp fun _ =>
        QComp.qbind (oracleQ m n (w * (m * n)) H) fun _ =>
          QComp.qbind (CPComp.unitary 1).toQComp fun _ =>
            measProj (diagB (finalAcc g)) (diagB_conjTranspose _) (diagB_mul_self _)) := by
  intro B
  set σ := oraclePerm m n (w * (m * n)) H * finalPerm p with hσ
  have hstate : (CPComp.unitary 1).toQComp.branch () ((oracleQ m n (w * (m * n)) H).branch ()
      ((CPComp.unitary (permUnitary (finalPerm p))).toQComp.branch ()
        (kr (ancE m n w (m * n)) B (ancProj 0)))) =
      (kr (ancE m n w (m * n)) B (ancProj 0)).submatrix σ.symm σ.symm := by
    change (1 : Matrix _ _ ℂ) * ((oracleU m n (w * (m * n)) H : Matrix _ _ ℂ) *
      ((permUnitary (finalPerm p) : Matrix _ _ ℂ) * kr (ancE m n w (m * n)) B (ancProj 0) *
        (permUnitary (finalPerm p) : Matrix _ _ ℂ)ᴴ) *
      (oracleU m n (w * (m * n)) H : Matrix _ _ ℂ)ᴴ) * (1 : Matrix _ _ ℂ)ᴴ = _
    rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one, oracleU_eq_permUnitary,
      ← permUnitary_conj σ, hσ, ← permUnitary_mul, Submonoid.coe_mul, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  simp only [qbind_unit_branch, measProj_branch_true]
  rw [hstate, trace_diagB_conj, trace_diagB_conj, ← Equiv.sum_comp σ]
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [← (finalRegIdx m n w).sum_comp, Fintype.sum_prod_type, ← (oracleIndex m n w).sum_comp]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single (0, 0)]
  · obtain ⟨⟨x, y⟩, z⟩ := t
    simp [hσ, finalPerm_finalRegIdx, finalPermAux, oraclePerm_finalRegIdx, finalAcc,
      kr_finalRegIdx_apply, ancProj, finProdEquiv_zero_zero]
  · intro a _ ha
    have hne : finProdEquiv m n a ≠ 0 := by
      rw [← finProdEquiv_zero_zero]
      exact fun h => ha ((finProdEquiv m n).injective h)
    simp [kr_finalRegIdx_apply, ancProj, hne]
  · simp

/-- The adversary `B` with one more query after the last operation of its last segment: the
    permutation unitary of `finalPerm p` moves the query register into an ancilla started at
    `(0, 0)` and writes `p i` into the query register, the query writes `H (p i)` into the value
    register, and the final projector is the one of `finalAcc g`. Each other segment starts
    with the dummy query of the trivial round. -/
def QAdvMRGen.withFinalQuery (B : QAdvMRGen m n w q k c a) (p : Fin (m * n * w) → Fin m)
    (g : Fin (m * n * w) → Fin n → Bool) : QAdvMRGen m n (w * (m * n)) (q + 1) k c a where
  seg := Fin.snoc (α := fun _ => Fin (q + 1 + 1) → CPComp (m * n * (w * (m * n))) Unit)
    (fun j : Fin k => segOps (trivR (m * n * w)) (fun _ => 0) (fun _ _ => 0)
      (liftOps (B.seg j.castSucc) (B.seg_tp j.castSucc)))
    (finalOps (liftOps (B.seg (Fin.last k)) (B.seg_tp (Fin.last k)))
      (CPComp.unitary (permUnitary (finalPerm p))) (CPComp.unitary 1))
  seg_tp j i := by
    induction j using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]
      exact isTP_finalOps _ (fun i => isTP_liftCh _ _ _)
        (CPComp.unitary (permUnitary (finalPerm p))) (CPComp.unitary 1)
        (isTP_unitaryChannel _) (isTP_unitaryChannel _) i
    | cast j =>
      rw [Fin.snoc_castSucc]
      exact isTP_segOps _ _ _ _ (fun i => isTP_liftCh _ _ _) i
  rounds j := liftRA (ancE m n w (m * n)) (B.rounds j)
  init := liftInit B.init
  final := diagB (finalAcc g)
  final_conjTranspose := diagB_conjTranspose _
  final_mul_self := diagB_mul_self _

/-- The final query computes the test that reads the oracle: at every oracle `H` and round
    function `f`, `B.withFinalQuery p g` accepts with the probability of `B` with the final
    test `g i (H (p i))`. -/
theorem prOutMRGen_withFinalQuery_eq (B : QAdvMRGen m n w q k c a)
    (p : Fin (m * n * w) → Fin m) (g : Fin (m * n * w) → Fin n → Bool) (H : Fin m → Fin n)
    (f : Fin c → Fin a) :
    prOutMRGen (B.withFinalQuery p g) H f =
      prOutMRGen (B.withFinalB fun i => g i (H (p i))) H f := by
  have hD : ∀ j : Fin k, PresAncQ (ancE m n w (m * n))
      (chainG (oracleQ m n w H) q fun i => (B.seg j.castSucc i).toQComp)
      (chainG (oracleQ m n (w * (m * n)) H) (q + 1)
        fun i => ((B.withFinalQuery p g).seg j.castSucc i).toQComp) := by
    intro j
    have h := presAncQ_seg H (trivR (m * n * w)) (fun _ => 0) (fun _ _ => 0) (B.seg j.castSucc)
      (liftOps (B.seg j.castSucc) (B.seg_tp j.castSucc)) fun i => liftsQ_liftCh _ _ _
    rw [roundU_trivR, QComp.qpure_qbind] at h
    simpa only [QAdvMRGen.withFinalQuery, Fin.snoc_castSucc] using h
  have hF : FinalRelQ (ancE m n w (m * n))
      (QComp.qbind (chainG (oracleQ m n w H) q fun i => (B.seg (Fin.last k) i).toQComp)
        fun _ => (B.withFinalB fun i => g i (H (p i))).measure)
      (QComp.qbind (chainG (oracleQ m n (w * (m * n)) H) (q + 1)
        fun i => ((B.withFinalQuery p g).seg (Fin.last k) i).toQComp)
        fun _ => (B.withFinalQuery p g).measure) := by
    simp only [QAdvMRGen.withFinalQuery, Fin.snoc_last, chainG_finalOps, QComp.qbind_assoc]
    exact finalRelQ_qbind (liftsQ_chainG _ (liftsQ_oracleQ_padE rfl H) q _ _
      fun i => liftsQ_liftCh _ _ _).presAncQ (finalRelQ_finalStep p g H)
  have h := finalRelQ_mrChainG (ancE m n w (m * n)) (oracleQ m n w H)
    (oracleQ m n (w * (m * n)) H) f (B.withFinalB fun i => g i (H (p i))).measure
    (B.withFinalQuery p g).measure k (fun j i => (B.seg j i).toQComp)
    (fun j i => ((B.withFinalQuery p g).seg j i).toQComp) B.rounds
    (B.withFinalQuery p g).rounds hD hF fun j => liftsQ_roundU_liftRA _ _ f
  exact congrArg (fun t : ℂ => ENNReal.ofReal t.re) (h B.init.val)

/-- The diagonal test of the flattened adversary that reads the oracle at the point `p i` of
    the basis state `i` is the final query of the recorded adversary: at every oracle `H` and
    round function `f`, it accepts with the probability of
    `(recordGen A fun _ => true).withFinalQuery p G`, which has `q + 1` queries per segment. -/
theorem prOut_withFinalB_toQAdv_eq_prOutMRGen_finalQuery [NeZero c] (A : QAdvMR m n w q k c a)
    (f : Fin c → Fin a) (p : Fin (m * n * ancW c k w) → Fin m)
    (G : Fin (m * n * ancW c k w) → Fin n → Bool) (H : Fin m → Fin n) :
    prOut ((toQAdv A f).withFinalB fun i => G i (H (p i))) H =
      prOutMRGen ((recordGen A fun _ => true).withFinalQuery p G) H f := by
  rw [prOut_withFinalB_toQAdv_eq, prOutMRGen_withFinalQuery_eq]
  rfl

/-- A final test of the flattened adversary that reads the oracle at a point given by the
    basis state is the acceptance probability of a general multi-round adversary with one more
    query per segment, the same for every oracle and round function. -/
theorem exists_prOutMRGen_finalQuery [NeZero c] (A : QAdvMR m n w q k c a)
    (p : Fin (m * n * ancW c k w) → Fin m) (G : Fin (m * n * ancW c k w) → Fin n → Bool) :
    ∃ B' : QAdvMRGen m n (ancW c k w * (m * n)) (q + 1) k c a, ∀ H f,
      prOut ((toQAdv A f).withFinalB fun i => G i (H (p i))) H = prOutMRGen B' H f :=
  ⟨_, fun H f => prOut_withFinalB_toQAdv_eq_prOutMRGen_finalQuery A f p G H⟩

end Final

end CatCrypt.Quantum.QROM
