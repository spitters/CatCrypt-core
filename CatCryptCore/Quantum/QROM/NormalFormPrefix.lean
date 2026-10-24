/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.KEMAdvNormalFormMR
public import CatCryptCore.Quantum.QROM.QOwcpaAuxMeasured

/-!
# The normal form cut at a query

`prOutMR_nfMR` states that the normal form `nfMR` of a multi-round adversary
outputs `1` with the probability of the adversary. This module states the same
for the multi-round run cut at a flat query index: the normal form, cut at `j`,
has its query register in `S` with the probability that the adversary, cut at
`j`, has.

## Main results

* `backMul_of_lt`, `frontMul_castLE` — a cut of a segment before its last
  unitary does not see `backMul`, and sees `frontMul` at its first unitary
* `mrPrefix_frontMul_branch` — a unitary merged into the first unitary of the
  head is applied before the cut chain
* `trace_nfPrefix` — the cut chain of the normal form agrees with the cut chain
  of the rounds `R` on every observable `X ⊗ 1`
* `prOutPrefixMR_nfMR`, `prOutPrefixMR_nfKEM` — the normal form, cut at a query,
  has the query-register probability of the adversary
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
  CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.Measurement

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Cuts of merged segments -/

section Cut

variable {d : ℕ}

/-- Before the last unitary, `backMul` leaves a segment unchanged. -/
theorem backMul_of_lt (V : Matrix.unitaryGroup (Fin d) ℂ) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (i : Fin (q + 1)),
      (i : ℕ) < q → backMul V q U i = U i
  | 0, _, i, h => absurd h (Nat.not_lt_zero _)
  | q + 1, U, i, h => by
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      show backMul V q (Fin.tail U) i = U i.succ
      exact backMul_of_lt V q (Fin.tail U) i (by simpa using h)

/-- The cut of a segment with `W` merged into its first unitary is the cut of
the segment with `W` merged into its first unitary. -/
theorem frontMul_castLE {q j : ℕ} (W : Matrix.unitaryGroup (Fin d) ℂ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (h : j + 1 ≤ q + 1) :
    (fun i : Fin (j + 1) => frontMul W U (Fin.castLE h i)) =
      frontMul W fun i : Fin (j + 1) => U (Fin.castLE h i) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    show frontMul W U (Fin.castLE h i.succ) = Fin.tail (fun i : Fin (j + 1) => U (Fin.castLE h i)) i
    have : Fin.castLE h i.succ = (Fin.castLE (by omega) i : Fin q).succ := Fin.ext (by simp)
    rw [this]
    rfl

variable {c a q : ℕ}

theorem mrPrefix_frontMul_branch (O : QComp d Bool) (f : Fin c → Fin a) (W : Matrix.unitaryGroup (Fin d) ℂ) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (j : Fin (flatQ q k q₀)) (b : Bool)
      (ρ : Matrix (Fin d) (Fin d) ℂ),
      (mrPrefix O f k q₀ (frontMul W head) tail R j).branch b ρ =
        (mrPrefix O f k q₀ head tail R j).branch b
          ((W : Matrix (Fin d) (Fin d) ℂ) * ρ * (W : Matrix (Fin d) (Fin d) ℂ)ᴴ)
  | 0, q₀, head, tail, R, j, b, ρ => by
    show (scChain O j fun i => frontMul W head (Fin.castLE _ i)).branch b ρ =
      (scChain O j fun i => head (Fin.castLE _ i)).branch b _
    rw [frontMul_castLE, scChain_frontMul, qbind_unit_branch, unitaryChannel_branch_apply]
  | k + 1, q₀, head, tail, R, j, b, ρ => by
    by_cases h : (j : ℕ) < q₀
    · simp only [mrPrefix, dite_eq_left h]
      rw [frontMul_castLE, scChain_frontMul, qbind_unit_branch, unitaryChannel_branch_apply]
    · simp only [mrPrefix, dite_eq_right h]
      rw [scChain_frontMul, QComp.qbind_assoc, qbind_unit_branch, unitaryChannel_branch_apply]

/-- The cut multi-round chain after the head, at the branch level. -/
theorem mrPrefix_succ_branch (O : QComp d Bool) (f : Fin c → Fin a) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin (k + 1) → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin (k + 1) → ClassicalRound d c a) (j : Fin (flatQ q (k + 1) q₀)) (h : ¬ (j : ℕ) < q₀)
    (b : Bool) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (mrPrefix O f (k + 1) q₀ head tail R j).branch b ρ =
      ∑ b₁, ∑ b₂, if b = (b₁ || b₂) then
        (mrPrefix O f k q (tail 0) (Fin.tail tail) (Fin.tail R)
          ⟨j - q₀, flatQ_succ_sub_lt j.isLt h⟩).branch b₂
          ((roundU (R 0) f).branch () ((scChain O q₀ head).branch b₁ ρ)) else 0 := by
  simp only [mrPrefix, dite_eq_right h, qbind_branch_apply, tsum_fintype, Fintype.sum_unique,
    qpure_branch_apply]
  refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
  congr

end Cut

/-! ## The cut chain of the normal form -/

section Chain

variable {d E D c a K q : ℕ}

/-- The cut of a lifted head chain before its last unitary, on `σ ⊗ |t⟩⟨t|` and
seen through `X ⊗ 1`, is the cut of the head chain on `σ`. -/
theorem trace_nfPrefix_head (e : Fin (d * E) ≃ Fin D) (O : QComp d Bool) (O' : QComp D Bool)
    (hO : LiftsQ e O O') (q₀ j : ℕ) (hj : j < q₀) (V : Matrix.unitaryGroup (Fin D) ℂ)
    (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) (t : Fin E)
    (X σ : Matrix (Fin d) (Fin d) ℂ) (b : Bool) (h : j + 1 ≤ q₀ + 1) :
    (kr e X 1 * (scChain O' j fun i => backMul V q₀ (liftU e ∘ head) (Fin.castLE h i)).branch b
        (kr e σ (ancUnit t t))).trace =
      (X * (scChain O j fun i => head (Fin.castLE h i)).branch b σ).trace := by
  have hU : (fun i : Fin (j + 1) => backMul V q₀ (liftU e ∘ head) (Fin.castLE h i)) =
      liftU e ∘ fun i => head (Fin.castLE h i) := by
    funext i
    rw [backMul_of_lt V q₀ _ _ (by simp; omega)]
    rfl
  rw [hU, liftsQ_scChain e O O' hO j _ b σ (ancUnit t t), kr_mul, one_mul, trace_kr,
    trace_ancUnit, ite_eq_left rfl, mul_one]

/-- **The cut multi-round chain in normal form.** On `σ ⊗ |t⟩⟨t|` with `t` good
from `j₀`, the cut chain of the normal-form segments and `slotRound` agrees with
the cut chain of the rounds `R` on `σ` on every observable `X ⊗ 1` and every
branch. -/
theorem trace_nfPrefix (e : Fin (d * E) ≃ Fin D) (S : SlotData E c a K) (O : QComp d Bool)
    (O' : QComp D Bool) (hO : LiftsQ e O O') (f : Fin c → Fin a) :
    ∀ (k j₀ q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (Vs : Fin (k + 1) → Matrix.unitaryGroup (Fin D) ℂ)
      (Ws : Fin k → Matrix.unitaryGroup (Fin D) ℂ), j₀ + k ≤ K →
      (∀ j : Fin k, Vs j.castSucc = copyU e S (R j)) →
      (∀ j : Fin k, Ws j = ansCtrlU e S (j₀ + j) (R j)) →
      ∀ t, S.Good j₀ t → ∀ (X σ : Matrix (Fin d) (Fin d) ℂ) (b : Bool) (jj : Fin (flatQ q k q₀)),
      (kr e X 1 * (mrPrefix O' f k q₀ (backMul (Vs 0) q₀ (liftU e ∘ head))
          (fun j => frontMul (Ws j) (backMul (Vs j.succ) q (liftU e ∘ tail j)))
          (fun _ => slotRound e S) jj).branch b (kr e σ (ancUnit t t))).trace =
        (X * (mrPrefix O f k q₀ head tail R jj).branch b σ).trace
  | 0, j₀, q₀, head, tail, R, Vs, Ws, _, _, _, t, _, X, σ, b, jj =>
    trace_nfPrefix_head e O O' hO q₀ jj (by simpa [flatQ] using jj.isLt) (Vs 0) head t X σ b _
  | k + 1, j₀, q₀, head, tail, R, Vs, Ws, hk, hV, hW, t, ht, X, σ, b, jj => by
    by_cases hlt : (jj : ℕ) < q₀
    · simp only [mrPrefix, dite_eq_left hlt]
      exact trace_nfPrefix_head e O O' hO q₀ jj hlt (Vs 0) head t X σ b _
    rw [mrPrefix_succ_branch _ _ _ _ _ _ _ _ hlt, mrPrefix_succ_branch _ _ _ _ _ _ _ _ hlt]
    simp_rw [Finset.mul_sum, trace_sum]
    refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
    split_ifs
    · have hV0 : Vs 0 = copyU e S (R 0) := hV 0
      have hW0 : Ws 0 = ansCtrlU e S j₀ (R 0) := hW 0
      rw [scChain_backMul_branch, liftsQ_scChain e O O' hO q₀ head b₁ σ (ancUnit t t), hV0]
      show (kr e X 1 * (mrPrefix O' f k q (frontMul (Ws 0) (backMul (Vs 1) q (liftU e ∘ tail 0)))
        (fun j => frontMul (Ws j.succ) (backMul (Vs j.succ.succ) q (liftU e ∘ Fin.tail tail j)))
        (fun _ => slotRound e S) _).branch b₂ _).trace = _
      rw [mrPrefix_frontMul_branch, hW0, block_conj e S j₀ j₀ (R 0) f _ t ht, map_sum,
        Finset.mul_sum, trace_sum, roundU_branch, map_sum, Finset.mul_sum, trace_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      exact trace_nfPrefix e S O O' hO f k (j₀ + 1) q (tail 0) (Fin.tail tail) (Fin.tail R)
        (fun j => Vs j.succ) (fun j => Ws j.succ) (by omega)
        (fun j => by rw [Fin.succ_castSucc]; exact hV j.succ)
        (fun j => by
          rw [hW j.succ, Fin.val_succ]
          congr 1
          omega)
        _ (S.good_swap j₀ t (by omega) ht y (f y)) X _ b₂ _
    · simp

end Chain

/-! ## The normal form cut at a query -/

section NF

variable {m n W E W' q k c a : ℕ} [NeZero n]

/-- **The normal form, cut at a query, has the query-register probability of
`A` cut at the same query**, for an initial basis state `t₀` good from slot `0`. -/
theorem prOutPrefixMR_nfMR (hW : W * E = W') (S : SlotData E c a k) (t₀ : Fin E)
    (ht₀ : S.Good 0 t₀) (A : QAdvMR m n W q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (Sq : Finset (Fin m)) (j : Fin (flatQ q k q)) :
    prOutPrefixMR (nfMR (padE m n hW) S t₀ A) H f Sq j = prOutPrefixMR A H f Sq j := by
  subst hW
  rw [prOutPrefixMR_eq_trace, prOutPrefixMR_eq_trace, projS_lift]
  refine congrArg (fun t : ℂ => ENNReal.ofReal t.re) ?_
  show (kr (ancE m n W E) (projS m n W Sq) 1 * (mrPrefix (scOracleQ m n (W * E) H ∅) f k q
      (frontMul 1 (backMul (nfV (ancE m n W E) S A.rounds 0) q (liftU (ancE m n W E) ∘ A.seg 0)))
      (fun j => frontMul (nfW (ancE m n W E) S A.rounds j.succ)
        (backMul (nfV (ancE m n W E) S A.rounds j.succ) q
          (liftU (ancE m n W E) ∘ Fin.tail A.seg j)))
      (fun _ => slotRound (ancE m n W E) S) j).branch false
        (kr (ancE m n W E) A.init.val (ancProj t₀))).trace = _
  rw [mrPrefix_frontMul_branch]
  simp only [OneMemClass.coe_one, one_mul, conjTranspose_one, mul_one, ← ancUnit_self]
  exact trace_nfPrefix (ancE m n W E) S _ _ (liftsQ_scOracleQ H ∅) f k 0 q (A.seg 0)
    (Fin.tail A.seg) A.rounds _ _ (by omega)
    (fun j => by simp [nfV]) (fun j => by simp [nfW]) t₀ ht₀ (projS m n W Sq)
    A.init.val false j

variable {m₁ m₂ w : ℕ} {PK C K : Type} [NeZero (m₁ + m₂)] [NeZero c] [NeZero a]

/-- The normal form of a KEM adversary, cut at a query, has the query-register
probability of the adversary. -/
theorem prOutPrefixMR_nfKEM (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (pk : PK) (cs : C) (κ : K)
    (H : Fin (m₁ + m₂) → Fin n) (f : Fin c → Fin a) (Sq : Finset (Fin (m₁ + m₂)))
    (j : Fin (flatQ q k q)) :
    prOutPrefixMR ((nfKEM A).run pk cs κ) H f Sq j = prOutPrefixMR (A.run pk cs κ) H f Sq j :=
  prOutPrefixMR_nfMR _ _ _ (nfStart_good (m₁ + m₂) n c a k) _ H f Sq j

end NF

end CatCrypt.Quantum.QROM

end

end
