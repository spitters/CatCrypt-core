/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.KEMAdvGeneral

/-!
# The unitary, pure-state normal form of a general multi-round adversary

Every general multi-round adversary `A : QAdvMRGen m n w q k c a` has a unitary
multi-round adversary `normalForm A : QAdvMR m n (w * nfDim m n w q k) q k c a`
with a pure initial state and the acceptance probability of `A` in every oracle
`H` and every round function `f`. The query counts `q` and `k`, the round
alphabets `c` and `a` and the query register `m * n` are type indices of both
adversaries and are the same. A general KEM adversary `A : KEMQAdvGen …` has the
KEM adversary `dilateKEM A : KEMQAdv …` with the same IND-CCA advantage.

## Construction

Let `d = m * n * w` and `r = d * d`. Every local operation of `A` is written as
a complete Kraus family of `r` operators (`krausOf`), and the adversary is
carried as a `QAdvMRK`, whose local operations are unitaries or Kraus families
of `r` operators (`KOp`).

* Purification (`QAdvMRK.purify`): every operation is tensored with `1` on an
  ancilla of dimension `d`, and the initial state is a purification of the
  initial state of `A`.
* Dilation (`QAdvMRK.step`, `QAdvMRK.dilL`): the local operations are processed
  one position at a time, in the order of `segPos k q`. A step appends an
  ancilla of dimension `r` to the work register, replaces the operation at the
  processed position by a unitary whose ancilla partial trace on
  `ρ ⊗ |0⟩⟨0|` is the operation (`exists_unitary_of_kraus`), tensors every other
  operation, round and the final projector with `1`, and tensors the initial
  state with `|0⟩⟨0|`. A tensored Kraus family `{K i ⊗ 1}` still has `r`
  operators, so every step uses an ancilla of dimension `r`.

After the `(k + 1) * (q + 1)` steps every operation is a unitary. The ancilla
dimension is `nfDim m n w q k = d * r ^ ((k + 1) * (q + 1))`.

## Main definitions

* `KOp d r`, `KOp.toCP`, `KOp.lift`, `KOp.dil` — a unitary or a Kraus family of
  `r` operators, its channel, its lift along an ancilla and its dilation
* `QAdvMRK` — a multi-round adversary whose local operations are `KOp`s
* `QAdvMRK.ofGen`, `QAdvMRK.toGen`, `QAdvMRK.toMR`
* `QAdvMRK.purify`, `QAdvMRK.step`, `QAdvMRK.dilL`
* `dilate A` — the unitary adversary of `A` without purification
* `normalForm A` — the unitary adversary of `A` with a pure initial state
* `dilateKEM A` — the KEM adversary of a general KEM adversary
* `prWinKEMGen`, `qINDCCAAdvantageGen` — the IND-CCA game of a general KEM
  adversary

## Main results

* `prOutMRGen_of_liftsQ`, `prOutMRGen_of_dilatesQ` — a general adversary whose
  operations lift, or lift except at one position where they dilate, those of
  another has its acceptance probability
* `prOutMR_dilate` — `dilate A` accepts with the probability of `A`
* `dilate_init_pure` — `dilate A` has a pure initial state when `A` has one
* `prOutMR_normalForm`, `normalForm_init_pure`
* `prOutMR_dilateKEM_run`, `qINDCCAAdvantage_dilateKEM`
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.UnitaryChannel
  CatCrypt.Quantum.Stinespring

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Kraus channels -/

section Kraus

variable {d r c D : ℕ}

/-- The channel `ρ ↦ ∑ i, K i ρ (K i)ᴴ` of a complete Kraus family, with the
outcome discarded. -/
def krausChQ (K : Fin r → Matrix (Fin d) (Fin d) ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) :
    QComp d Unit :=
  QComp.qbind (QComp.ofKraus K hK) fun _ => QComp.qpure ()

theorem krausChQ_branch (K : Fin r → Matrix (Fin d) (Fin d) ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    (u : Unit) (M : Matrix (Fin d) (Fin d) ℂ) :
    (krausChQ K hK).branch u M = ∑ i, K i * M * (K i)ᴴ := by
  unfold krausChQ
  rw [qbind_branch_apply, tsum_fintype]
  simp only [qpure_branch_apply, QComp.ofKraus_branch]
  simp

/-- The channel of a complete Kraus family as a completely positive instrument. -/
def krausCh (K : Fin r → Matrix (Fin d) (Fin d) ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) :
    CPComp d Unit :=
  CPComp.mk' (krausChQ K hK) fun u => isCPMap_krausSum _ _ (krausChQ_branch K hK u)

theorem isTP_krausCh (K : Fin r → Matrix (Fin d) (Fin d) ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) :
    IsTP ((krausCh K hK).toQComp.branch ()) := fun M => by
  show ((krausChQ K hK).branch () M).trace = M.trace
  rw [krausChQ_branch, trace_sum]
  simp_rw [trace_mul_cycle _ M]
  rw [← trace_sum, ← Finset.sum_mul, hK, one_mul]

/-- The family `{K i ⊗ 1}` is complete when `{K i}` is. -/
theorem kr_kraus_complete (e : Fin (d * c) ≃ Fin D) {K : Fin r → Matrix (Fin d) (Fin d) ℂ}
    (hK : ∑ i, (K i)ᴴ * K i = 1) : ∑ i, (kr e (K i) 1)ᴴ * kr e (K i) 1 = 1 := by
  simp only [kr_conjTranspose, kr_mul, conjTranspose_one, one_mul]
  rw [← kr_sum_left, hK, kr_one]

/-- The channel of `{K i ⊗ 1}` lifts the channel of `{K i}`. -/
theorem liftsQ_krausCh (e : Fin (d * c) ≃ Fin D) (K : Fin r → Matrix (Fin d) (Fin d) ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    LiftsQ e (krausCh K hK).toQComp
      (krausCh (fun i => kr e (K i) 1) (kr_kraus_complete e hK)).toQComp := by
  intro u B E
  show (krausChQ _ _).branch u (kr e B E) = kr e ((krausChQ K hK).branch u B) E
  rw [krausChQ_branch, krausChQ_branch, kr_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kr_conjTranspose, kr_mul, kr_mul, conjTranspose_one, one_mul, mul_one]

end Kraus

/-! ## Local operations: unitaries and Kraus families -/

/-- A local operation on `Fin d`: a unitary, or a complete Kraus family of `r`
operators. -/
abbrev KOp (d r : ℕ) : Type :=
  Matrix.unitaryGroup (Fin d) ℂ ⊕ {K : Fin r → Matrix (Fin d) (Fin d) ℂ // ∑ i, (K i)ᴴ * K i = 1}

namespace KOp

variable {d r c D : ℕ}

/-- The channel of a local operation. -/
def toCP : KOp d r → CPComp d Unit
  | .inl U => CPComp.unitary U
  | .inr K => krausCh K.1 K.2

theorem isTP : ∀ o : KOp d r, IsTP (o.toCP.toQComp.branch ())
  | .inl U => isTP_unitaryChannel U
  | .inr K => isTP_krausCh K.1 K.2

/-- The operation tensored with `1` on the ancilla `Fin c`. -/
def lift (e : Fin (d * c) ≃ Fin D) : KOp d r → KOp D r
  | .inl U => .inl (liftU e U)
  | .inr K => .inr ⟨fun i => kr e (K.1 i) 1, kr_kraus_complete e K.2⟩

theorem liftsQ_lift (e : Fin (d * c) ≃ Fin D) :
    ∀ o : KOp d r, LiftsQ e o.toCP.toQComp (o.lift e).toCP.toQComp
  | .inl U => liftsQ_unitaryChannel e U
  | .inr K => liftsQ_krausCh e K.1 K.2

/-- The dilation on the ancilla `Fin r`: a Kraus family becomes a unitary whose
ancilla partial trace on `ρ ⊗ |0⟩⟨0|` is its channel; a unitary is tensored
with `1`. -/
def dil [NeZero r] (e : Fin (d * r) ≃ Fin D) : KOp d r → KOp D r
  | .inl U => .inl (liftU e U)
  | .inr K => .inl ⟨(exists_unitary_of_kraus e K.2).choose,
      (exists_unitary_of_kraus e K.2).choose_spec.1⟩

theorem dilatesQ_dil [NeZero r] (e : Fin (d * r) ≃ Fin D) :
    ∀ o : KOp d r, DilatesQ e o.toCP.toQComp (o.dil e).toCP.toQComp
  | .inl U => (liftsQ_unitaryChannel e U).dilatesQ
  | .inr K => fun u ρ => by
    show trAnc e ((unitaryChannel _).branch u (kr e ρ (ancProj 0))) =
      (krausChQ K.1 K.2).branch u ρ
    rw [krausChQ_branch]
    exact ((exists_unitary_of_kraus e K.2).choose_spec.2 ρ).symm

theorem isLeft_dil [NeZero r] (e : Fin (d * r) ≃ Fin D) :
    ∀ o : KOp d r, (o.dil e).isLeft = true
  | .inl _ => rfl
  | .inr _ => rfl

theorem isLeft_lift (e : Fin (d * c) ≃ Fin D) :
    ∀ o : KOp d r, o.isLeft = true → (o.lift e).isLeft = true
  | .inl _, _ => rfl
  | .inr _, h => h

/-- The unitary of a local operation, and `1` for a Kraus family. -/
def get : KOp d r → Matrix.unitaryGroup (Fin d) ℂ
  | .inl U => U
  | .inr _ => 1

theorem toCP_of_isLeft : ∀ o : KOp d r, o.isLeft = true → o.toCP = CPComp.unitary o.get
  | .inl _, _ => rfl
  | .inr _, h => absurd h (by simp)

end KOp

/-! ## Chains with one dilated operation -/

section DilChain

variable {d r D c a q : ℕ} [NeZero r]

/-- A chain whose operation at `p` dilates and whose other operations lift is a
dilation. -/
theorem dilatesQ_chainG (e : Fin (d * r) ≃ Fin D) {O : QComp d Unit} {O' : QComp D Unit}
    (hO : LiftsQ e O O') :
    ∀ (q : ℕ) (U : Fin (q + 1) → QComp d Unit) (U' : Fin (q + 1) → QComp D Unit)
      (p : Fin (q + 1)), DilatesQ e (U p) (U' p) → (∀ i, i ≠ p → LiftsQ e (U i) (U' i)) →
      DilatesQ e (chainG O q U) (chainG O' q U')
  | 0, _, _, p, hp, _ => by rwa [Fin.fin_one_eq_zero p] at hp
  | q + 1, U, U', p, hp, hU => by
    induction p using Fin.cases with
    | zero =>
      exact dilatesQ_qbind_liftsQ hp fun _ => liftsQ_qbind e hO fun _ =>
        liftsQ_chainG e hO q (Fin.tail U) (Fin.tail U') fun i => hU i.succ (Fin.succ_ne_zero i)
    | succ p =>
      exact liftsQ_qbind_dilatesQ (hU 0 (Fin.succ_ne_zero p).symm) fun _ =>
        liftsQ_qbind_dilatesQ hO fun _ =>
          dilatesQ_chainG e hO q (Fin.tail U) (Fin.tail U') p hp fun i hi =>
            hU i.succ fun h => hi (Fin.succ_injective _ h)

/-- A multi-round chain whose head operation at `p` dilates and whose other
operations and rounds lift is a dilation. -/
theorem dilatesQ_mrChainG_head (e : Fin (d * r) ≃ Fin D) {O : QComp d Unit}
    {O' : QComp D Unit} (hO : LiftsQ e O O') (f : Fin c → Fin a) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → QComp d Unit) (head' : Fin (q₀ + 1) → QComp D Unit)
    (tail : Fin k → Fin (q + 1) → QComp d Unit) (tail' : Fin k → Fin (q + 1) → QComp D Unit)
    (R : Fin k → ClassicalRound d c a) (R' : Fin k → ClassicalRound D c a) (p : Fin (q₀ + 1))
    (hp : DilatesQ e (head p) (head' p)) (hh : ∀ i, i ≠ p → LiftsQ e (head i) (head' i))
    (ht : ∀ j i, LiftsQ e (tail j i) (tail' j i))
    (hR : ∀ j, LiftsQ e (roundU (R j) f) (roundU (R' j) f)) :
    DilatesQ e (mrChainG O f k q₀ head tail R) (mrChainG O' f k q₀ head' tail' R') := by
  cases k with
  | zero => exact dilatesQ_chainG e hO q₀ head head' p hp hh
  | succ k =>
    exact dilatesQ_qbind_liftsQ (dilatesQ_chainG e hO q₀ head head' p hp hh) fun _ =>
      liftsQ_qbind e (hR 0) fun _ =>
        liftsQ_mrChainG e hO f k q (tail 0) (tail' 0) (Fin.tail tail) (Fin.tail tail')
          (Fin.tail R) (Fin.tail R') (ht 0) (fun j => ht j.succ) fun j => hR j.succ

/-- A multi-round chain whose tail operation at `(j, i)` dilates and whose other
operations and rounds lift is a dilation. -/
theorem dilatesQ_mrChainG_tail (e : Fin (d * r) ≃ Fin D) {O : QComp d Unit}
    {O' : QComp D Unit} (hO : LiftsQ e O O') (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (head' : Fin (q₀ + 1) → QComp D Unit)
      (tail : Fin k → Fin (q + 1) → QComp d Unit) (tail' : Fin k → Fin (q + 1) → QComp D Unit)
      (R : Fin k → ClassicalRound d c a) (R' : Fin k → ClassicalRound D c a)
      (j : Fin k) (i : Fin (q + 1)), DilatesQ e (tail j i) (tail' j i) →
      (∀ j' i', (j', i') ≠ (j, i) → LiftsQ e (tail j' i') (tail' j' i')) →
      (∀ i, LiftsQ e (head i) (head' i)) → (∀ j, LiftsQ e (roundU (R j) f) (roundU (R' j) f)) →
      DilatesQ e (mrChainG O f k q₀ head tail R) (mrChainG O' f k q₀ head' tail' R')
  | 0, _, _, _, _, _, _, _, j, _, _, _, _, _ => j.elim0
  | k + 1, q₀, head, head', tail, tail', R, R', j, i, hp, ht, hh, hR => by
    refine liftsQ_qbind_dilatesQ (liftsQ_chainG e hO q₀ head head' hh) fun _ =>
      liftsQ_qbind_dilatesQ (hR 0) fun _ => ?_
    induction j using Fin.cases with
    | zero =>
      exact dilatesQ_mrChainG_head e hO f k q (tail 0) (tail' 0) (Fin.tail tail)
        (Fin.tail tail') (Fin.tail R) (Fin.tail R') i hp
        (fun i' hi => ht 0 i' fun h => hi (congrArg Prod.snd h))
        (fun j' i' => ht j'.succ i' fun h => Fin.succ_ne_zero j' (congrArg Prod.fst h))
        fun j => hR j.succ
    | succ j =>
      exact dilatesQ_mrChainG_tail e hO f k q (tail 0) (tail' 0) (Fin.tail tail)
        (Fin.tail tail') (Fin.tail R) (Fin.tail R') j i hp
        (fun j' i' h => ht j'.succ i' fun h' =>
          h (Prod.ext (Fin.succ_injective _ (Prod.mk.inj h').1) (Prod.mk.inj h').2))
        (fun i' => ht 0 i' fun h => Fin.succ_ne_zero j (congrArg Prod.fst h).symm)
        fun j => hR j.succ

end DilChain

/-! ## Acceptance probabilities of lifted and dilated general adversaries -/

section GenStep

variable {m n W W' D q k c a : ℕ}

theorem liftsQ_oracleQ_padE [NeZero n] (hW : W * D = W') (H : Fin m → Fin n) :
    LiftsQ (padE m n hW) (oracleQ m n W H) (oracleQ m n W' H) := by
  subst hW
  have hOU : oracleU m n (W * D) H = liftU (ancE m n W D) (oracleU m n W H) :=
    Subtype.ext (oracleU_lift H)
  rw [oracleQ, oracleQ, hOU]
  exact liftsQ_unitaryChannel _ _

/-- The measurement of a projector equal to `P ⊗ 1` lifts the measurement of `P`. -/
theorem liftsQ_measProj_of_eq {d d' : ℕ} (e : Fin (d * D) ≃ Fin d')
    (P : Matrix (Fin d) (Fin d) ℂ) (P' : Matrix (Fin d') (Fin d') ℂ) (hP : P' = kr e P 1)
    (hH : Pᴴ = P) (hI : P * P = P) (hH' : P'ᴴ = P') (hI' : P' * P' = P') :
    LiftsQ e (measProj P hH hI) (measProj P' hH' hI') := by
  subst hP
  exact liftsQ_measProj e P hH hI hH' hI'

variable [NeZero n]

/-- A general adversary whose operations, rounds and final projector are lifts
of those of `B`, and whose initial state has the initial state of `B` as its
ancilla partial trace, accepts with the probability of `B`. -/
theorem prOutMRGen_of_liftsQ (hW : W * D = W') (B : QAdvMRGen m n W q k c a)
    (B' : QAdvMRGen m n W' q k c a)
    (hseg : ∀ j i, LiftsQ (padE m n hW) (B.seg j i).toQComp (B'.seg j i).toQComp)
    (hR : ∀ j, B'.rounds j = liftRA (padE m n hW) (B.rounds j))
    (hfin : B'.final = kr (padE m n hW) B.final 1)
    (hinit : trAnc (padE m n hW) B'.init.val = B.init.val) (H : Fin m → Fin n)
    (f : Fin c → Fin a) : prOutMRGen B' H f = prOutMRGen B H f := by
  have hL : LiftsQ (padE m n hW) (runMRGen B H f) (runMRGen B' H f) :=
    liftsQ_qbind _ (liftsQ_mrChainG _ (liftsQ_oracleQ_padE hW H) f k q _ _ _ _ _ _
      (fun i => hseg 0 i) (fun j i => hseg j.succ i)
      fun j => by rw [hR]; exact liftsQ_roundU_liftRA _ _ f)
      fun _ => liftsQ_measProj_of_eq _ _ _ hfin _ _ _ _
  unfold prOutMRGen prTrue_Q
  rw [← trace_trAnc (padE m n hW), hL.trAnc_branch, hinit]

/-- A general adversary whose operation at `p` dilates the one of `B`, whose
other operations, rounds and final projector are lifts of those of `B`, and
whose initial state is `ρ ⊗ |0⟩⟨0|` for the initial state `ρ` of `B`, accepts
with the probability of `B`. -/
theorem prOutMRGen_of_dilatesQ [NeZero D] (hW : W * D = W') (B : QAdvMRGen m n W q k c a)
    (B' : QAdvMRGen m n W' q k c a) (p : Fin (k + 1) × Fin (q + 1))
    (hp : DilatesQ (padE m n hW) (B.seg p.1 p.2).toQComp (B'.seg p.1 p.2).toQComp)
    (hseg : ∀ j i, (j, i) ≠ p → LiftsQ (padE m n hW) (B.seg j i).toQComp (B'.seg j i).toQComp)
    (hR : ∀ j, B'.rounds j = liftRA (padE m n hW) (B.rounds j))
    (hfin : B'.final = kr (padE m n hW) B.final 1)
    (hinit : B'.init.val = kr (padE m n hW) B.init.val (ancProj 0)) (H : Fin m → Fin n)
    (f : Fin c → Fin a) : prOutMRGen B' H f = prOutMRGen B H f := by
  have hRL : ∀ j, LiftsQ (padE m n hW) (roundU (B.rounds j) f) (roundU (B'.rounds j) f) :=
    fun j => by rw [hR]; exact liftsQ_roundU_liftRA _ _ f
  have hD : DilatesQ (padE m n hW) (runMRGen B H f) (runMRGen B' H f) := by
    refine dilatesQ_qbind_liftsQ ?_ fun _ => liftsQ_measProj_of_eq _ _ _ hfin _ _ _ _
    obtain ⟨j, i⟩ := p
    induction j using Fin.cases with
    | zero =>
      exact dilatesQ_mrChainG_head _ (liftsQ_oracleQ_padE hW H) f k q _ _ _ _ _ _ i hp
        (fun i' hi => hseg 0 i' fun h => hi (congrArg Prod.snd h))
        (fun j i' => hseg j.succ i' fun h => Fin.succ_ne_zero j (congrArg Prod.fst h)) hRL
    | succ j =>
      exact dilatesQ_mrChainG_tail _ (liftsQ_oracleQ_padE hW H) f k q _ _ _ _ _ _ j i hp
        (fun j' i' h => hseg j'.succ i' fun h' =>
          h (Prod.ext (Fin.succ_injective _ (Prod.mk.inj h').1) (Prod.mk.inj h').2))
        (fun i' => hseg 0 i' fun h => Fin.succ_ne_zero j (congrArg Prod.fst h).symm) hRL
  unfold prOutMRGen prTrue_Q
  rw [hinit, hD.trace_branch]

end GenStep

/-! ## Initial states on an extended register -/

section Init

variable {d c D : ℕ}

/-- A density matrix on `Fin d` has `d ≠ 0`. -/
theorem neZero_of_densityMatrix (ρ : DensityMatrix d) : NeZero d :=
  ⟨fun h => by
    subst h
    have h1 := ρ.tr_one
    simp [Matrix.trace] at h1⟩

/-- The state `ρ ⊗ |0⟩⟨0|`. -/
def ancInit [NeZero c] (e : Fin (d * c) ≃ Fin D) (ρ : DensityMatrix d) : DensityMatrix D where
  val := kr e ρ.val (ancProj 0)
  psd := kr_posSemidef _ ρ.psd (ancProj_posSemidef 0)
  tr_one := by rw [trace_kr, ρ.tr_one, trace_ancProj, one_mul]

/-- A purifying vector of `ρ` along `e`. -/
def purVecE (e : Fin (d * d) ≃ Fin D) (ρ : DensityMatrix d) : Fin D → ℂ :=
  (exists_purification e ρ.psd ρ.tr_one).choose

/-- The pure state of `purVecE e ρ`. -/
def purInit (e : Fin (d * d) ≃ Fin D) (ρ : DensityMatrix d) : DensityMatrix D where
  val := vecMulVec (purVecE e ρ) (star (purVecE e ρ))
  psd := posSemidef_vecMulVec_self_star _
  tr_one := by
    rw [trace_vecMulVec, dotProduct_comm]
    exact (exists_purification e ρ.psd ρ.tr_one).choose_spec.1

theorem trAnc_purInit (e : Fin (d * d) ≃ Fin D) (ρ : DensityMatrix d) :
    trAnc e (purInit e ρ).val = ρ.val :=
  (exists_purification e ρ.psd ρ.tr_one).choose_spec.2.symm

theorem ancInit_pure [NeZero c] (e : Fin (d * c) ≃ Fin D) (ρ : DensityMatrix d)
    (h : ∃ ψ, ρ.val = vecMulVec ψ (star ψ)) : ∃ ψ, (ancInit e ρ).val = vecMulVec ψ (star ψ) := by
  obtain ⟨ψ, hψ⟩ := h
  exact ⟨kv e ψ (Pi.single 0 1), by
    show kr e ρ.val (ancProj 0) = _
    rw [hψ, ancProj_zero_eq_vecMulVec, kr_vecMulVec]⟩

end Init

/-! ## Adversaries with unitary and Kraus local operations -/

/-- A multi-round adversary whose local operations are unitaries or complete
Kraus families of `r` operators, with the rounds, initial state and final
projector of `QAdvMR`. -/
structure QAdvMRK (m n W r q k c a : ℕ) where
  /-- The local operations of the segments. -/
  op : Fin (k + 1) → Fin (q + 1) → KOp (m * n * W) r
  /-- The rounds, round `j` between segments `j` and `j + 1`. -/
  rounds : Fin k → ClassicalRound (m * n * W) c a
  /-- The initial state. -/
  init : DensityMatrix (m * n * W)
  /-- The projector of the final measurement. -/
  final : Matrix (Fin (m * n * W)) (Fin (m * n * W)) ℂ
  final_conjTranspose : finalᴴ = final
  final_mul_self : final * final = final

namespace QAdvMRK

variable {m n w W W' r q k c a : ℕ}

/-- The general adversary of `B`. -/
def toGen (B : QAdvMRK m n W r q k c a) : QAdvMRGen m n W q k c a where
  seg j i := (B.op j i).toCP
  seg_tp j i := (B.op j i).isTP
  rounds := B.rounds
  init := B.init
  final := B.final
  final_conjTranspose := B.final_conjTranspose
  final_mul_self := B.final_mul_self

/-- The unitary adversary of `B`; a Kraus family is read as the unitary `1`. -/
def toMR (B : QAdvMRK m n W r q k c a) : QAdvMR m n W q k c a where
  seg j i := (B.op j i).get
  rounds := B.rounds
  init := B.init
  final := B.final
  final_conjTranspose := B.final_conjTranspose
  final_mul_self := B.final_mul_self

/-- `A` with every local operation written as a Kraus family of
`(m * n * w) * (m * n * w)` operators. -/
def ofGen (A : QAdvMRGen m n w q k c a) : QAdvMRK m n w (m * n * w * (m * n * w)) q k c a where
  op j i := .inr ⟨krausOf (A.seg j i), krausOf_complete _ (A.seg_tp j i)⟩
  rounds := A.rounds
  init := A.init
  final := A.final
  final_conjTranspose := A.final_conjTranspose
  final_mul_self := A.final_mul_self

theorem toGen_ofGen (A : QAdvMRGen m n w q k c a) : (ofGen A).toGen = A := by
  rcases A with ⟨seg, tp, R, ρ, F, h₁, h₂⟩
  simp only [toGen, ofGen, QAdvMRGen.mk.injEq, and_true]
  funext j i
  refine CPComp.ext (QComp.ext_fun fun u M => ?_)
  show (krausChQ _ _).branch u M = _
  rw [krausChQ_branch, krausOf_spec]

theorem toGen_toMR (B : QAdvMRK m n W r q k c a) (h : ∀ j i, (B.op j i).isLeft = true) :
    B.toMR.toGen = B.toGen := by
  simp only [QAdvMR.toGen, toMR, toGen, QAdvMRGen.mk.injEq, and_true]
  funext j i
  exact (KOp.toCP_of_isLeft _ (h j i)).symm

/-- Purification: every operation, round and the final projector tensored with
`1` on an ancilla of dimension `m * n * W`, and the initial state a
purification of the initial state of `B`. -/
def purify (hW : W * (m * n * W) = W') (B : QAdvMRK m n W r q k c a) :
    QAdvMRK m n W' r q k c a where
  op j i := (B.op j i).lift (padE m n hW)
  rounds j := liftRA (padE m n hW) (B.rounds j)
  init := purInit (padE m n hW) B.init
  final := kr (padE m n hW) B.final 1
  final_conjTranspose := by rw [kr_conjTranspose, B.final_conjTranspose, conjTranspose_one]
  final_mul_self := by rw [kr_mul, B.final_mul_self, one_mul]

/-- One dilation step at the position `p`: the operation at `p` dilated on a
fresh ancilla `Fin r`, every other operation, round and the final projector
tensored with `1`, and the initial state `ρ ⊗ |0⟩⟨0|`. -/
def step [NeZero r] (hW : W * r = W') (p : Fin (k + 1) × Fin (q + 1))
    (B : QAdvMRK m n W r q k c a) : QAdvMRK m n W' r q k c a where
  op j i := if (j, i) = p then (B.op j i).dil (padE m n hW) else (B.op j i).lift (padE m n hW)
  rounds j := liftRA (padE m n hW) (B.rounds j)
  init := ancInit (padE m n hW) B.init
  final := kr (padE m n hW) B.final 1
  final_conjTranspose := by rw [kr_conjTranspose, B.final_conjTranspose, conjTranspose_one]
  final_mul_self := by rw [kr_mul, B.final_mul_self, one_mul]

/-- The dilation steps at the positions of `l`, the last position of `l` first,
on the work registers `g 0, g 1, …`. -/
def dilL [NeZero r] (g : ℕ → ℕ) (hg : ∀ t, g t * r = g (t + 1)) (B : QAdvMRK m n (g 0) r q k c a) :
    (l : List (Fin (k + 1) × Fin (q + 1))) → QAdvMRK m n (g l.length) r q k c a
  | [] => B
  | p :: l => (dilL g hg B l).step (hg l.length) p

variable [NeZero n]

theorem prOutMRGen_purify (hW : W * (m * n * W) = W') (B : QAdvMRK m n W r q k c a)
    (H : Fin m → Fin n) (f : Fin c → Fin a) :
    prOutMRGen (B.purify hW).toGen H f = prOutMRGen B.toGen H f :=
  prOutMRGen_of_liftsQ hW B.toGen (B.purify hW).toGen (fun _ _ => KOp.liftsQ_lift _ _)
    (fun _ => rfl) rfl (trAnc_purInit _ _) H f

theorem prOutMRGen_step [NeZero r] (hW : W * r = W') (p : Fin (k + 1) × Fin (q + 1))
    (B : QAdvMRK m n W r q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    prOutMRGen (B.step hW p).toGen H f = prOutMRGen B.toGen H f := by
  refine prOutMRGen_of_dilatesQ hW B.toGen (B.step hW p).toGen p ?_ (fun j i h => ?_)
    (fun _ => rfl) rfl rfl H f
  · show DilatesQ _ (B.op p.1 p.2).toCP.toQComp
      (if (p.1, p.2) = p then _ else _ : KOp _ r).toCP.toQComp
    rw [ite_eq_left rfl]
    exact KOp.dilatesQ_dil _ _
  · show LiftsQ _ (B.op j i).toCP.toQComp (if (j, i) = p then _ else _ : KOp _ r).toCP.toQComp
    rw [ite_eq_right h]
    exact KOp.liftsQ_lift _ _

theorem prOutMRGen_dilL [NeZero r] (g : ℕ → ℕ) (hg : ∀ t, g t * r = g (t + 1))
    (B : QAdvMRK m n (g 0) r q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    ∀ l, prOutMRGen (B.dilL g hg l).toGen H f = prOutMRGen B.toGen H f
  | [] => rfl
  | p :: l => (prOutMRGen_step _ p _ H f).trans (prOutMRGen_dilL g hg B H f l)

omit [NeZero n] in
/-- After the steps at the positions of `l`, the operations at those positions
are unitaries. -/
theorem isLeft_dilL [NeZero r] (g : ℕ → ℕ) (hg : ∀ t, g t * r = g (t + 1))
    (B : QAdvMRK m n (g 0) r q k c a) :
    ∀ l p, p ∈ l → ((B.dilL g hg l).op p.1 p.2).isLeft = true
  | [], _, h => absurd h List.not_mem_nil
  | p' :: l, p, h => by
    show (if (p.1, p.2) = p' then _ else _ : KOp _ r).isLeft = true
    split_ifs with hp
    · exact KOp.isLeft_dil _ _
    · rcases List.mem_cons.1 h with rfl | h'
      · exact absurd rfl hp
      · exact KOp.isLeft_lift _ _ (isLeft_dilL g hg B l p h')

omit [NeZero n] in
theorem dilL_init_pure [NeZero r] (g : ℕ → ℕ) (hg : ∀ t, g t * r = g (t + 1))
    (B : QAdvMRK m n (g 0) r q k c a) (hB : ∃ ψ, B.init.val = vecMulVec ψ (star ψ)) :
    ∀ l, ∃ ψ, (B.dilL g hg l).init.val = vecMulVec ψ (star ψ)
  | [] => hB
  | _ :: l => ancInit_pure _ _ (dilL_init_pure g hg B hB l)

theorem prOutMR_toMR (B : QAdvMRK m n W r q k c a) (h : ∀ j i, (B.op j i).isLeft = true)
    (H : Fin m → Fin n) (f : Fin c → Fin a) : prOutMR B.toMR H f = prOutMRGen B.toGen H f := by
  rw [← prOutMRGen_toGen, toGen_toMR B h]

end QAdvMRK

/-! ## The normal form -/

section NormalForm

/-- The positions of the local operations, each once. -/
def segPos (k q : ℕ) : List (Fin (k + 1) × Fin (q + 1)) :=
  (Finset.univ : Finset (Fin (k + 1) × Fin (q + 1))).toList

theorem length_segPos (k q : ℕ) : (segPos k q).length = (k + 1) * (q + 1) := by
  simp [segPos]

theorem mem_segPos {k q : ℕ} (p : Fin (k + 1) × Fin (q + 1)) : p ∈ segPos k q := by
  simp [segPos]

/-- The work register `W * r * ⋯ * r` after `t` dilation steps. -/
def dilW (W r : ℕ) : ℕ → ℕ
  | 0 => W
  | t + 1 => dilW W r t * r

theorem dilW_succ (W r t : ℕ) : dilW W r t * r = dilW W r (t + 1) := rfl

theorem dilW_zero (W r : ℕ) : W = dilW W r 0 := rfl

theorem dilW_eq (W r : ℕ) : ∀ t, dilW W r t = W * r ^ t
  | 0 => by simp [dilW]
  | t + 1 => by rw [dilW, dilW_eq W r t, pow_succ, Nat.mul_assoc]

/-- The ancilla dimension of `dilate`: `((m * n * w)²) ^ ((k + 1) * (q + 1))`. -/
def dilDim (m n w q k : ℕ) : ℕ := (m * n * w * (m * n * w)) ^ ((k + 1) * (q + 1))

/-- The ancilla dimension of `normalForm`:
`(m * n * w) * ((m * n * w)²) ^ ((k + 1) * (q + 1))`. -/
def nfDim (m n w q k : ℕ) : ℕ := m * n * w * dilDim m n w q k

variable {m n w q k c a : ℕ}

theorem dilW_dilDim (m n w q k : ℕ) :
    dilW w (m * n * w * (m * n * w)) (segPos k q).length = w * dilDim m n w q k := by
  rw [dilW_eq, length_segPos, dilDim]

theorem dilW_nfDim (m n w q k : ℕ) :
    dilW (w * (m * n * w)) (m * n * w * (m * n * w)) (segPos k q).length =
      w * nfDim m n w q k := by
  rw [dilW_eq, length_segPos, nfDim, dilDim, Nat.mul_assoc]

/-- The dilated adversary of `A`: every local operation of `A` replaced by a
unitary on its own ancilla of dimension `(m * n * w)²`, the initial state
`ρ ⊗ |0⟩⟨0|`. It has `q` queries per segment and `k` rounds, as `A`. -/
def dilate (A : QAdvMRGen m n w q k c a) : QAdvMR m n (w * dilDim m n w q k) q k c a :=
  haveI := neZero_of_densityMatrix A.init
  castMR (dilW_dilDim m n w q k)
    ((QAdvMRK.ofGen A).dilL (dilW w _) (dilW_succ w _) (segPos k q)).toMR

/-- The unitary, pure-state normal form of `A`: `A` purified on an ancilla of
dimension `m * n * w`, then dilated. It has `q` queries per segment and `k`
rounds, as `A`. -/
def normalForm (A : QAdvMRGen m n w q k c a) : QAdvMR m n (w * nfDim m n w q k) q k c a :=
  haveI := neZero_of_densityMatrix A.init
  castMR (dilW_nfDim m n w q k)
    (((QAdvMRK.ofGen A).purify (dilW_zero _ _)).dilL (dilW (w * (m * n * w)) _)
      (dilW_succ _ _) (segPos k q)).toMR

theorem dilate_init_pure (A : QAdvMRGen m n w q k c a)
    (hA : ∃ ψ, A.init.val = vecMulVec ψ (star ψ)) :
    ∃ ψ, (dilate A).init.val = vecMulVec ψ (star ψ) := by
  have := neZero_of_densityMatrix A.init
  exact castMR_init_pure _ _ (QAdvMRK.dilL_init_pure _ _ _ hA _)

theorem normalForm_init_pure (A : QAdvMRGen m n w q k c a) :
    ∃ ψ, (normalForm A).init.val = vecMulVec ψ (star ψ) := by
  have := neZero_of_densityMatrix A.init
  exact castMR_init_pure _ _ (QAdvMRK.dilL_init_pure _ _ _ ⟨_, rfl⟩ _)

variable [NeZero n]

/-- The dilated adversary accepts with the probability of `A` in every oracle
and every round function. -/
theorem prOutMR_dilate (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    prOutMR (dilate A) H f = prOutMRGen A H f := by
  have := neZero_of_densityMatrix A.init
  rw [dilate, prOutMR_castMR]
  exact (QAdvMRK.prOutMR_toMR _ (fun j i => QAdvMRK.isLeft_dilL _ _ _ _ (j, i) (mem_segPos _))
    H f).trans ((QAdvMRK.prOutMRGen_dilL _ _ _ H f _).trans
      (congrArg (prOutMRGen · H f) (QAdvMRK.toGen_ofGen A)))

/-- The normal form accepts with the probability of `A` in every oracle and
every round function. -/
theorem prOutMR_normalForm (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) : prOutMR (normalForm A) H f = prOutMRGen A H f := by
  have := neZero_of_densityMatrix A.init
  rw [normalForm, prOutMR_castMR]
  exact (QAdvMRK.prOutMR_toMR _ (fun j i => QAdvMRK.isLeft_dilL _ _ _ _ (j, i) (mem_segPos _))
    H f).trans ((QAdvMRK.prOutMRGen_dilL _ _ _ H f _).trans
      ((QAdvMRK.prOutMRGen_purify _ _ H f).trans
        (congrArg (prOutMRGen · H f) (QAdvMRK.toGen_ofGen A))))

end NormalForm

/-! ## General KEM adversaries -/

section KEM

theorem dilW_nfDim_two (M n w q k : ℕ) :
    dilW (w * (M * n * (2 * w))) (M * n * (2 * w) * (M * n * (2 * w))) (segPos k q).length =
      w * nfDim M n (2 * w) q k := by
  rw [dilW_eq, length_segPos, nfDim, dilDim, Nat.mul_assoc]

/-- The work register `2 * (X * r * ⋯ * r)` after `t` dilation steps. -/
def kemW (X r t : ℕ) : ℕ := 2 * dilW X r t

theorem kemW_succ (X r t : ℕ) : kemW X r t * r = kemW X r (t + 1) :=
  Nat.mul_assoc _ _ _

theorem kemW_zero (w X r : ℕ) : 2 * w * X = kemW (w * X) r 0 :=
  Nat.mul_assoc _ _ _

theorem kemW_nfDim (M n w q k : ℕ) :
    kemW (w * (M * n * (2 * w))) (M * n * (2 * w) * (M * n * (2 * w))) (segPos k q).length =
      2 * (w * nfDim M n (2 * w) q k) :=
  congrArg (2 * ·) (dilW_nfDim_two M n w q k)

variable {M n q k c a : ℕ}

/-- Purification keeps the output projector `winBitProj`. -/
theorem final_purify_winBitProj {w r : ℕ} (B : QAdvMRK M n (2 * w) r q k c a)
    (hB : B.final = winBitProj M n w) :
    (B.purify (kemW_zero w (M * n * (2 * w)) r)).final = winBitProj M n (w * (M * n * (2 * w))) := by
  show kr _ B.final 1 = _
  rw [hB]
  exact (winBitProj_pad M n w _ _).symm

/-- The dilation steps keep the output projector `winBitProj` on the work
registers `kemW X r t`. -/
theorem final_dilL_winBitProj {X r : ℕ} [NeZero r] (B : QAdvMRK M n (kemW X r 0) r q k c a)
    (hB : B.final = winBitProj M n X) :
    ∀ l, (B.dilL (kemW X r) (kemW_succ X r) l).final = winBitProj M n (dilW X r l.length)
  | [] => hB
  | _ :: l => by
    show kr _ (B.dilL _ _ l).final 1 = _
    rw [final_dilL_winBitProj B hB l]
    exact (winBitProj_pad M n _ r _).symm

theorem castMR_final_winBitProj {Y Y' : ℕ} (hY : Y = Y') (h : 2 * Y = 2 * Y')
    (B : QAdvMR M n (2 * Y) q k c a) (hB : B.final = winBitProj M n Y) :
    (castMR h B).final = winBitProj M n Y' := by
  subst hY
  exact hB

variable {m₁ m₂ w : ℕ} {PK C K : Type}

/-- The unitary, pure-state KEM adversary of a general KEM adversary: at each
public key, challenge ciphertext and challenge key, the adversary purified on an
ancilla of dimension `(m₁ + m₂) * n * (2 * w)` inside the work register, then
dilated. It has `q` queries per segment and `k` decapsulation rounds, as `A`. -/
def dilateKEM (A : KEMQAdvGen m₁ m₂ n w q k c a PK C K) :
    KEMQAdv m₁ m₂ n (w * nfDim (m₁ + m₂) n (2 * w) q k) q k c a PK C K where
  run pk cs κ :=
    haveI := neZero_of_densityMatrix (A.run pk cs κ).init
    castMR (kemW_nfDim (m₁ + m₂) n w q k)
      (((QAdvMRK.ofGen (A.run pk cs κ)).purify (kemW_zero w _ _)).dilL
        (kemW _ _) (kemW_succ _ _) (segPos k q)).toMR
  final_eq pk cs κ := by
    have := neZero_of_densityMatrix (A.run pk cs κ).init
    exact castMR_final_winBitProj (dilW_nfDim_two (m₁ + m₂) n w q k) _ _
      (final_dilL_winBitProj _ (final_purify_winBitProj _ (A.final_eq pk cs κ)) _)
  pure pk cs κ := by
    have := neZero_of_densityMatrix (A.run pk cs κ).init
    exact castMR_init_pure _ _ (QAdvMRK.dilL_init_pure (kemW _ _) (kemW_succ _ _) _ ⟨_, rfl⟩ _)

variable [NeZero n]

/-- At every public key, challenge ciphertext and challenge key, the adversary
of `dilateKEM A` accepts with the probability of `A` in every oracle and every
round function. -/
theorem prOutMR_dilateKEM_run (A : KEMQAdvGen m₁ m₂ n w q k c a PK C K) (pk : PK) (cs : C)
    (κ : K) (H : Fin (m₁ + m₂) → Fin n) (f : Fin c → Fin a) :
    prOutMR ((dilateKEM A).run pk cs κ) H f = prOutMRGen (A.run pk cs κ) H f := by
  have := neZero_of_densityMatrix (A.run pk cs κ).init
  refine (prOutMR_castMR _ _ H f).trans ?_
  exact (QAdvMRK.prOutMR_toMR _ (fun j i => QAdvMRK.isLeft_dilL _ _ _ _ (j, i) (mem_segPos _))
    H f).trans ((QAdvMRK.prOutMRGen_dilL _ _ _ H f _).trans
      ((QAdvMRK.prOutMRGen_purify _ _ H f).trans
        (congrArg (prOutMRGen · H f) (QAdvMRK.toGen_ofGen _))))

end KEM

/-! ## The IND-CCA game of a general KEM adversary -/

section Game

open CatCrypt.Crypto.PKE.Games (Scheme)

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [Fintype Z] [Fintype K] [Nonempty K] [DecidableEq C] (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero n]

/-- `prWinKEM` for a general KEM adversary, with `prOutMRGen` in place of
`prOutMR`. -/
def prWinKEMGen (A : KEMQAdvGen m₁ m₂ n w q k c a PK C K) (b : Bool) : ℝ≥0∞ :=
  ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
    prOutMRGen (A.run i.1.1 (kemChal P hpk eG eKR i) (kemKey hpk eG eKR i b)) (kemOracle i)
      (kemDecaps P hpk eG eJ eKR eC eKa i)

/-- The quantum IND-CCA advantage of a general KEM adversary. -/
def qINDCCAAdvantageGen (A : KEMQAdvGen m₁ m₂ n w q k c a PK C K) : ℝ≥0∞ :=
  absDiff (prWinKEMGen P hpk eG eJ eKR eC eKa A true)
    (prWinKEMGen P hpk eG eJ eKR eC eKa A false)

theorem prWinKEM_dilateKEM (A : KEMQAdvGen m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinKEM P hpk eG eJ eKR eC eKa (dilateKEM A) b = prWinKEMGen P hpk eG eJ eKR eC eKa A b := by
  unfold prWinKEM prWinKEMGen
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prOutMR_dilateKEM_run]

/-- `dilateKEM A` has the IND-CCA advantage of the general KEM adversary `A`. -/
theorem qINDCCAAdvantage_dilateKEM (A : KEMQAdvGen m₁ m₂ n w q k c a PK C K) :
    qINDCCAAdvantage P hpk eG eJ eKR eC eKa (dilateKEM A) =
      qINDCCAAdvantageGen P hpk eG eJ eKR eC eKa A := by
  rw [qINDCCAAdvantage, qINDCCAAdvantageGen, prWinKEM_dilateKEM, prWinKEM_dilateKEM]

/-- A unitary KEM adversary read as a general one has its IND-CCA advantage. -/
theorem qINDCCAAdvantageGen_toGen (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    qINDCCAAdvantageGen P hpk eG eJ eKR eC eKa A.toGen =
      qINDCCAAdvantage P hpk eG eJ eKR eC eKa A := by
  simp only [qINDCCAAdvantageGen, qINDCCAAdvantage, prWinKEMGen, prWinKEM, KEMQAdv.toGen_run]

end Game

end CatCrypt.Quantum.QROM
