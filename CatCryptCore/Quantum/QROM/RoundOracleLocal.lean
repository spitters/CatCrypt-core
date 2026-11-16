/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.RoundOracle

/-!
# Classical rounds up to bad, conditioned on the oracle and the other outcomes

Two statements about a multi-round adversary `A : QAdvMRGen m n w q k c a`
whose round function `f` is random together with the oracle `H`.

* Unread outcomes: `Pr[out = 1 ∧ no round outcome lies in Y]` depends on the
  round function only outside `Y`.
* Up to bad, local form: if `f' ω` agrees with `f ω` outside `E ω`, and at
  every outcome `y` the event `y ∈ E ω`, conditioned on `H ω` and on the values
  of `f ω` outside `y`, has probability at most `λ`, then the average
  acceptance probabilities with `f` and with `f'` differ by at most `k · λ`.

The second statement rests on the first-read weight `badW1 f D`: the sum over
the rounds of the weight of the outcomes in `D`, each measured on the part of
the state whose earlier round outcomes all lie outside `D`. It depends on `f`
only outside `D`, it bounds the change of the acceptance probability when `f`
is changed inside `D`, it is at most the sum of its values at the singletons
of `D`, and its values at all singletons sum to at most `k`.

## Main definitions

* `badW1 O f D k q₀ head tail R σ` — the first-read weight of `D`
* `mrPartG O f Y k q₀ head tail R σ` — the state of the multi-round chain on
  the branches whose round outcomes all lie outside `Y`
* `prOutAvoidMRGen A H f Y` — `Pr[out = 1 ∧ no round outcome lies in Y]`

## Main results

* `abs_eff_mrChainG_sub_le_badW1` — two round functions agreeing outside `D`
  change the value of a final measurement by at most `badW1`
* `prOutMRGen_congr_unread` — `prOutAvoidMRGen` depends on `f` only outside `Y`
* `prOutAvoidMRGen_le_prOutMRGen`, `prOutMRGen_le_prOutAvoidMRGen_add` —
  `prOutAvoidMRGen ≤ prOutMRGen ≤ prOutAvoidMRGen + badW1`
* `rounds_upto_bad_local` — the averaged round bound `k · λ` under the
  conditional hypothesis
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.UnitaryChannel

noncomputable section

namespace CatCrypt.Quantum.QROM

section Rounds

variable {d c a : ℕ}

theorem roundPart_add (R : ClassicalRound d c a) (f : Fin c → Fin a) (D : Finset (Fin c))
    (σ τ : Matrix (Fin d) (Fin d) ℂ) :
    roundPart R f D (σ + τ) = roundPart R f D σ + roundPart R f D τ := by
  simp [roundPart, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

/-- For `S ⊆ T`, the part of the round channel at `T` is the part at `S` plus
the part at `T \ S`. -/
theorem roundPart_of_subset (R : ClassicalRound d c a) (f : Fin c → Fin a)
    {S T : Finset (Fin c)} (h : S ⊆ T) (σ : Matrix (Fin d) (Fin d) ℂ) :
    roundPart R f T σ = roundPart R f S σ + roundPart R f (T \ S) σ := by
  exact (Finset.sum_sdiff h).symm.trans (add_comm _ _)

/-- The first-read weight of `D`: the sum over the rounds of the weight of the
outcomes in `D`, each measured on the part of the state, in the chain with the
classical function `f`, whose earlier round outcomes all lie outside `D`. -/
def badW1 (O : QComp d Unit) (f : Fin c → Fin a) (D : Finset (Fin c)) {q : ℕ} :
    (k : ℕ) → (q₀ : ℕ) → (Fin (q₀ + 1) → QComp d Unit) →
      (Fin k → Fin (q + 1) → QComp d Unit) → (Fin k → ClassicalRound d c a) →
      Matrix (Fin d) (Fin d) ℂ → ℝ
  | 0, _, _, _, _, _ => 0
  | k + 1, q₀, head, tail, R, σ =>
    roundBad (R 0) D ((chainG O q₀ head).branch () σ) +
      badW1 O f D k q (tail 0) (Fin.tail tail) (Fin.tail R)
        (roundPart (R 0) f Dᶜ ((chainG O q₀ head).branch () σ))

/-- The state of the multi-round chain with the classical function `f` on the
branches whose round outcomes all lie outside `Y`. -/
def mrPartG (O : QComp d Unit) (f : Fin c → Fin a) (Y : Finset (Fin c)) {q : ℕ} :
    (k : ℕ) → (q₀ : ℕ) → (Fin (q₀ + 1) → QComp d Unit) →
      (Fin k → Fin (q + 1) → QComp d Unit) → (Fin k → ClassicalRound d c a) →
      Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ
  | 0, q₀, head, _, _, σ => (chainG O q₀ head).branch () σ
  | k + 1, q₀, head, tail, R, σ =>
    mrPartG O f Y k q (tail 0) (Fin.tail tail) (Fin.tail R)
      (roundPart (R 0) f Yᶜ ((chainG O q₀ head).branch () σ))

variable {q : ℕ}

theorem badW1_add (O : QComp d Unit) (f : Fin c → Fin a) (D : Finset (Fin c)) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
      (R : Fin k → ClassicalRound d c a) (σ τ : Matrix (Fin d) (Fin d) ℂ),
      badW1 O f D k q₀ head tail R (σ + τ) =
        badW1 O f D k q₀ head tail R σ + badW1 O f D k q₀ head tail R τ
  | 0, _, _, _, _, _, _ => by simp [badW1]
  | k + 1, q₀, head, tail, R, σ, τ => by
    simp only [badW1, map_add, roundBad_add, roundPart_add,
      badW1_add O f D k q (tail 0) (Fin.tail tail) (Fin.tail R)]
    ring

theorem badW1_nonneg (O : QComp d Unit) (f : Fin c → Fin a) (D : Finset (Fin c)) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
      (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ), σ.PosSemidef →
      0 ≤ badW1 O f D k q₀ head tail R σ
  | 0, _, _, _, _, _, _ => le_rfl
  | k + 1, q₀, head, tail, R, σ, hσ => by
    have h₁ := (chainG O q₀ head).branch_psd () σ hσ
    exact add_nonneg (roundBad_nonneg _ _ h₁)
      (badW1_nonneg O f D k q (tail 0) (Fin.tail tail) (Fin.tail R) _
        (roundPart_posSemidef (R 0) f Dᶜ h₁))

theorem badW1_le_add (O : QComp d Unit) (f : Fin c → Fin a) (D : Finset (Fin c)) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
    (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ)
    {τ : Matrix (Fin d) (Fin d) ℂ} (hτ : τ.PosSemidef) :
    badW1 O f D k q₀ head tail R σ ≤ badW1 O f D k q₀ head tail R (σ + τ) := by
  simpa [badW1_add] using badW1_nonneg O f D k q₀ head tail R τ hτ

/-- The first-read weight of `D` depends on the classical function only
outside `D`. -/
theorem badW1_congr (O : QComp d Unit) {f f' : Fin c → Fin a} {D : Finset (Fin c)}
    (hf : ∀ y, y ∉ D → f' y = f y) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
      (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ),
      badW1 O f' D k q₀ head tail R σ = badW1 O f D k q₀ head tail R σ
  | 0, _, _, _, _, _ => rfl
  | k + 1, q₀, head, tail, R, σ => by
    simp only [badW1, roundPart_congr (R 0) hf,
      badW1_congr O hf k q (tail 0) (Fin.tail tail) (Fin.tail R)]

/-- The first-read weight of `D` is at most the sum of the first-read weights
of the singletons of `D`. -/
theorem badW1_le_sum_singleton (O : QComp d Unit) (f : Fin c → Fin a) :
    ∀ (D : Finset (Fin c)) (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit)
      (tail : Fin k → Fin (q + 1) → QComp d Unit)
      (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ), σ.PosSemidef →
      badW1 O f D k q₀ head tail R σ ≤ ∑ y ∈ D, badW1 O f {y} k q₀ head tail R σ
  | D, 0, _, _, _, _, _, _ => by simp [badW1]
  | D, k + 1, q₀, head, tail, R, σ, hσ => by
    set σ₁ := (chainG O q₀ head).branch () σ with hσ₁def
    have hσ₁ : σ₁.PosSemidef := (chainG O q₀ head).branch_psd () σ hσ
    have ih := badW1_le_sum_singleton O f D k q (tail 0) (Fin.tail tail) (Fin.tail R)
      (roundPart (R 0) f Dᶜ σ₁) (roundPart_posSemidef (R 0) f Dᶜ hσ₁)
    have hmono : ∀ y ∈ D,
        badW1 O f {y} k q (tail 0) (Fin.tail tail) (Fin.tail R) (roundPart (R 0) f Dᶜ σ₁) ≤
          badW1 O f {y} k q (tail 0) (Fin.tail tail) (Fin.tail R)
            (roundPart (R 0) f {y}ᶜ σ₁) := by
      intro y hy
      rw [roundPart_of_subset (R 0) f
        (Finset.compl_subset_compl.mpr (Finset.singleton_subset_iff.mpr hy))]
      exact badW1_le_add O f {y} k q _ _ _ _ (roundPart_posSemidef (R 0) f _ hσ₁)
    simp only [badW1]
    rw [← hσ₁def, roundBad_eq_sum_singleton, Finset.sum_add_distrib]
    exact add_le_add le_rfl (ih.trans (Finset.sum_le_sum hmono))

/-- The first-read weights of all singletons sum to at most `k · tr σ`. -/
theorem sum_badW1_singleton_le (O : QComp d Unit) (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
      (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ), σ.PosSemidef →
      ∑ y, badW1 O f {y} k q₀ head tail R σ ≤ k * σ.trace.re
  | 0, _, _, _, _, σ, _ => by simp [badW1]
  | k + 1, q₀, head, tail, R, σ, hσ => by
    set σ₁ := (chainG O q₀ head).branch () σ with hσ₁def
    have h₁ : σ₁.PosSemidef := (chainG O q₀ head).branch_psd () σ hσ
    set ρ := (roundU (R 0) f).branch () σ₁ with hρdef
    have h₂ : ρ.PosSemidef := (roundU (R 0) f).branch_psd () _ h₁
    have ih := sum_badW1_singleton_le O f k q (tail 0) (Fin.tail tail) (Fin.tail R) ρ h₂
    have hmono : ∀ y : Fin c,
        badW1 O f {y} k q (tail 0) (Fin.tail tail) (Fin.tail R) (roundPart (R 0) f {y}ᶜ σ₁) ≤
          badW1 O f {y} k q (tail 0) (Fin.tail tail) (Fin.tail R) ρ := by
      intro y
      rw [hρdef, roundU_branch_eq_add (R 0) f {y} σ₁]
      exact badW1_le_add O f {y} k q _ _ _ _ (roundPart_posSemidef (R 0) f _ h₁)
    have hrb : ∑ y : Fin c, roundBad (R 0) {y} σ₁ = σ₁.trace.re := by
      rw [← roundBad_eq_sum_singleton, roundBad_univ]
    have t₁ := trace_re_branch_unit_le (chainG O q₀ head) hσ
    have t₂ := trace_re_branch_unit_le (roundU (R 0) f) h₁
    have t₀ := trace_re_nonneg_of_posSemidef hσ
    have t₃ := trace_re_nonneg_of_posSemidef h₁
    have hs := Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) => hmono y
    simp only [badW1]
    rw [← hσ₁def, Finset.sum_add_distrib, hrb]
    push_cast
    nlinarith

/-- Two classical functions of the rounds that agree outside `D` change the
value `tr (E_true (C σ))` of a final measurement `E` after the multi-round
chain `C` by at most the first-read weight `badW1` of `D` in the chain with
`f`. -/
theorem abs_eff_mrChainG_sub_le_badW1 (O : QComp d Unit) (E : QComp d Bool)
    {f f' : Fin c → Fin a} {D : Finset (Fin c)} (hf : ∀ y, y ∉ D → f' y = f y) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
      (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ), σ.PosSemidef →
      |(E.branch true ((mrChainG O f k q₀ head tail R).branch () σ)).trace.re -
        (E.branch true ((mrChainG O f' k q₀ head tail R).branch () σ)).trace.re| ≤
        badW1 O f D k q₀ head tail R σ
  | 0, _, _, _, _, _, _ => by simp [mrChainG, badW1]
  | k + 1, q₀, head, tail, R, σ, hσ => by
    set σ₁ := (chainG O q₀ head).branch () σ with hσ₁def
    have hσ₁ : σ₁.PosSemidef := (chainG O q₀ head).branch_psd () σ hσ
    set rest := mrChainG O f k q (tail 0) (Fin.tail tail) (Fin.tail R)
    set rest' := mrChainG O f' k q (tail 0) (Fin.tail tail) (Fin.tail R)
    have hC : (mrChainG O f (k + 1) q₀ head tail R).branch () σ =
        rest.branch () ((roundU (R 0) f).branch () σ₁) := by
      simp only [mrChainG, qbind_unit_branch, rest, σ₁]
    have hC' : (mrChainG O f' (k + 1) q₀ head tail R).branch () σ =
        rest'.branch () ((roundU (R 0) f').branch () σ₁) := by
      simp only [mrChainG, qbind_unit_branch, rest', σ₁]
    have hs := roundU_branch_eq_add (R 0) f D σ₁
    have hs' := roundU_branch_eq_add (R 0) f' D σ₁
    rw [roundPart_congr (R 0) hf] at hs'
    have hG := roundPart_posSemidef (R 0) f Dᶜ hσ₁
    have hB := roundPart_posSemidef (R 0) f D hσ₁
    have hB' := roundPart_posSemidef (R 0) f' D hσ₁
    have ih := abs_eff_mrChainG_sub_le_badW1 O E hf k q (tail 0) (Fin.tail tail) (Fin.tail R)
      _ hG
    have a₁ := trace_re_nonneg_of_posSemidef (E.branch_psd true _ (rest.branch_psd () _ hB))
    have a₁' := trace_re_nonneg_of_posSemidef (E.branch_psd true _ (rest'.branch_psd () _ hB'))
    have a₂ := (trace_re_branch_true_le E (rest.branch_psd () _ hB)).trans
      (trace_re_branch_unit_le rest hB)
    have a₂' := (trace_re_branch_true_le E (rest'.branch_psd () _ hB')).trans
      (trace_re_branch_unit_le rest' hB')
    rw [trace_roundPart] at a₂ a₂'
    rw [hC, hC', hs, hs', map_add, map_add, map_add, map_add, trace_add, trace_add,
      Complex.add_re, Complex.add_re]
    simp only [badW1]
    rw [abs_le] at ih ⊢
    constructor <;> linarith [ih.1, ih.2]

theorem mrPartG_congr (O : QComp d Unit) {f f' : Fin c → Fin a} {Y : Finset (Fin c)}
    (hf : ∀ y, y ∉ Y → f' y = f y) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
      (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ),
      mrPartG O f' Y k q₀ head tail R σ = mrPartG O f Y k q₀ head tail R σ
  | 0, _, _, _, _, _ => rfl
  | k + 1, q₀, head, tail, R, σ => by
    simp only [mrPartG, roundPart_congr (R 0) hf,
      mrPartG_congr O hf k q (tail 0) (Fin.tail tail) (Fin.tail R)]

theorem mrPartG_posSemidef (O : QComp d Unit) (f : Fin c → Fin a) (Y : Finset (Fin c)) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
      (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ), σ.PosSemidef →
      (mrPartG O f Y k q₀ head tail R σ).PosSemidef
  | 0, q₀, head, _, _, σ, hσ => (chainG O q₀ head).branch_psd () σ hσ
  | k + 1, q₀, head, tail, R, σ, hσ =>
    mrPartG_posSemidef O f Y k q (tail 0) (Fin.tail tail) (Fin.tail R) _
      (roundPart_posSemidef (R 0) f Yᶜ ((chainG O q₀ head).branch_psd () σ hσ))

/-- The value of a final measurement on the multi-round chain lies between its
value on the branches whose round outcomes all lie outside `Y` and that value
plus the first-read weight of `Y`. -/
theorem eff_mrChainG_sub_mrPartG_mem (O : QComp d Unit) (E : QComp d Bool)
    (f : Fin c → Fin a) (Y : Finset (Fin c)) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (tail : Fin k → Fin (q + 1) → QComp d Unit)
      (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ), σ.PosSemidef →
      0 ≤ (E.branch true ((mrChainG O f k q₀ head tail R).branch () σ)).trace.re -
          (E.branch true (mrPartG O f Y k q₀ head tail R σ)).trace.re ∧
        (E.branch true ((mrChainG O f k q₀ head tail R).branch () σ)).trace.re -
          (E.branch true (mrPartG O f Y k q₀ head tail R σ)).trace.re ≤
          badW1 O f Y k q₀ head tail R σ
  | 0, _, _, _, _, _, _ => by simp [mrChainG, mrPartG, badW1]
  | k + 1, q₀, head, tail, R, σ, hσ => by
    set σ₁ := (chainG O q₀ head).branch () σ with hσ₁def
    have hσ₁ : σ₁.PosSemidef := (chainG O q₀ head).branch_psd () σ hσ
    set rest := mrChainG O f k q (tail 0) (Fin.tail tail) (Fin.tail R)
    have hC : (mrChainG O f (k + 1) q₀ head tail R).branch () σ =
        rest.branch () ((roundU (R 0) f).branch () σ₁) := by
      simp only [mrChainG, qbind_unit_branch, rest, σ₁]
    have hs := roundU_branch_eq_add (R 0) f Y σ₁
    have hG := roundPart_posSemidef (R 0) f Yᶜ hσ₁
    have hB := roundPart_posSemidef (R 0) f Y hσ₁
    have ih := eff_mrChainG_sub_mrPartG_mem O E f Y k q (tail 0) (Fin.tail tail)
      (Fin.tail R) _ hG
    have a₁ := trace_re_nonneg_of_posSemidef (E.branch_psd true _ (rest.branch_psd () _ hB))
    have a₂ := (trace_re_branch_true_le E (rest.branch_psd () _ hB)).trans
      (trace_re_branch_unit_le rest hB)
    rw [trace_roundPart] at a₂
    rw [hC, hs, map_add, map_add, trace_add, Complex.add_re]
    simp only [mrPartG, badW1]
    constructor <;> linarith [ih.1, ih.2]

end Rounds

section RoundsAdv

variable {m n w q k c a : ℕ} [NeZero n]

/-- The probability that the run outputs `1` and no round outcome lies in `Y`. -/
def prOutAvoidMRGen (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (Y : Finset (Fin c)) : ℝ≥0∞ :=
  ENNReal.ofReal (A.measure.branch true (mrPartG (oracleQ m n w H) f Y k q
    (fun i => (A.seg 0 i).toQComp) (fun j i => (Fin.tail A.seg j i).toQComp) A.rounds
    A.init.val)).trace.re

theorem prOutMRGen_eq_ofReal (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) :
    prOutMRGen A H f = ENNReal.ofReal (A.measure.branch true
      ((mrChainG (oracleQ m n w H) f k q (fun i => (A.seg 0 i).toQComp)
        (fun j i => (Fin.tail A.seg j i).toQComp) A.rounds).branch () A.init.val)).trace.re := by
  unfold prOutMRGen prTrue_Q runMRGen
  rw [qbind_unit_branch]

/-- Unread outcomes: the probability that the run outputs `1` and no round
outcome lies in `Y` is the same for two round functions that agree outside
`Y`. -/
theorem prOutMRGen_congr_unread (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n)
    {f f' : Fin c → Fin a} {Y : Finset (Fin c)} (hf : ∀ y, y ∉ Y → f' y = f y) :
    prOutAvoidMRGen A H f' Y = prOutAvoidMRGen A H f Y := by
  unfold prOutAvoidMRGen
  rw [mrPartG_congr _ hf]

theorem prOutAvoidMRGen_le_prOutMRGen (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (Y : Finset (Fin c)) :
    prOutAvoidMRGen A H f Y ≤ prOutMRGen A H f := by
  rw [prOutMRGen_eq_ofReal, prOutAvoidMRGen]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := (eff_mrChainG_sub_mrPartG_mem (oracleQ m n w H) A.measure f Y k q
    (fun i => (A.seg 0 i).toQComp) (fun j i => (Fin.tail A.seg j i).toQComp) A.rounds _
    A.init.psd).1
  linarith

theorem prOutMRGen_le_prOutAvoidMRGen_add (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (Y : Finset (Fin c)) :
    prOutMRGen A H f ≤ prOutAvoidMRGen A H f Y +
      ENNReal.ofReal (badW1 (oracleQ m n w H) f Y k q (fun i => (A.seg 0 i).toQComp)
        (fun j i => (Fin.tail A.seg j i).toQComp) A.rounds A.init.val) := by
  rw [prOutMRGen_eq_ofReal, prOutAvoidMRGen]
  have h := eff_mrChainG_sub_mrPartG_mem (oracleQ m n w H) A.measure f Y k q
    (fun i => (A.seg 0 i).toQComp) (fun j i => (Fin.tail A.seg j i).toQComp) A.rounds _
    A.init.psd
  have h₀ := trace_re_nonneg_of_posSemidef (A.measure.branch_psd true _
    (mrPartG_posSemidef (oracleQ m n w H) f Y k q (fun i => (A.seg 0 i).toQComp)
      (fun j i => (Fin.tail A.seg j i).toQComp) A.rounds _ A.init.psd))
  rw [← ENNReal.ofReal_add h₀ (h.1.trans h.2)]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [h.2]

/-- Two round functions that agree outside `D` change the acceptance
probability of a general adversary by at most the first-read weight of `D`,
measured in the run with `f`. -/
theorem absDiff_prOutMRGen_le_badW1 (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n)
    {f f' : Fin c → Fin a} {D : Finset (Fin c)} (hf : ∀ y, y ∉ D → f' y = f y) :
    absDiff (prOutMRGen A H f) (prOutMRGen A H f') ≤
      ENNReal.ofReal (badW1 (oracleQ m n w H) f D k q (fun i => (A.seg 0 i).toQComp)
        (fun j i => (Fin.tail A.seg j i).toQComp) A.rounds A.init.val) := by
  rw [prOutMRGen_eq_ofReal, prOutMRGen_eq_ofReal]
  have hp := A.init.psd
  have h₀ : ∀ C : QComp (m * n * w) Unit,
      0 ≤ (A.measure.branch true (C.branch () A.init.val)).trace.re := fun C =>
    trace_re_nonneg_of_posSemidef (A.measure.branch_psd true _ (C.branch_psd () _ hp))
  refine (absDiff_ofReal_le (h₀ _) (h₀ _)).trans (ENNReal.ofReal_le_ofReal ?_)
  exact abs_eff_mrChainG_sub_le_badW1 _ A.measure hf k q _ _ _ _ hp

/-- Grouping a sum by the fibres of `κ`: if `V` is constant on the fibres and
on each fibre the weight of `p` is at most `λ` times the weight of the fibre,
then `∑ μ · [p] · V ≤ λ · ∑ μ · V`. -/
theorem sum_mul_boole_mul_le_of_fiber {Ω K : Type} [Fintype Ω] [DecidableEq K]
    (κ : Ω → K) (μ V : Ω → ℝ≥0∞) (p : Ω → Prop) [DecidablePred p] (lam : ℝ≥0∞)
    (hV : ∀ ω ω', κ ω = κ ω' → V ω = V ω')
    (h : ∀ ω₀, ∑ ω, μ ω * (if κ ω = κ ω₀ then 1 else 0) * (if p ω then 1 else 0) ≤
      lam * ∑ ω, μ ω * (if κ ω = κ ω₀ then 1 else 0)) :
    ∑ ω, μ ω * (if p ω then 1 else 0) * V ω ≤ lam * ∑ ω, μ ω * V ω := by
  have key : ∀ F : Ω → ℝ≥0∞, ∑ ω, F ω =
      ∑ j ∈ Finset.univ.image κ, ∑ ω ∈ Finset.univ.filter (fun ω => κ ω = j), F ω :=
    fun F => (Finset.sum_fiberwise_of_maps_to
      (fun x _ => Finset.mem_image_of_mem κ (Finset.mem_univ x)) F).symm
  rw [key, key, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  obtain ⟨ω₀, -, rfl⟩ := Finset.mem_image.mp hj
  have hs : ∀ g : Ω → ℝ≥0∞, ∑ ω ∈ Finset.univ.filter (fun ω => κ ω = κ ω₀), g ω * V ω =
      (∑ ω ∈ Finset.univ.filter (fun ω => κ ω = κ ω₀), g ω) * V ω₀ := fun g =>
    (Finset.sum_congr rfl fun ω hω => by rw [hV _ _ (Finset.mem_filter.mp hω).2]).trans
      (Finset.sum_mul _ _ _).symm
  rw [hs, hs, ← mul_assoc]
  gcongr
  simpa only [Finset.sum_filter, mul_ite, mul_one, mul_zero, ← ite_and, and_comm] using h ω₀

/-- Up to bad in the classical rounds, conditioned on the oracle and the other
outcomes: let `f' ω` agree with `f ω` outside `E ω`, and let the event
`y ∈ E ω`, conditioned on `H ω` and on the values of `f ω` outside `y`, have
probability at most `λ` under `μ`, at every outcome `y`. Then the average
acceptance probabilities of `A` with `f` and with `f'` differ by at most
`k · λ`. -/
theorem rounds_upto_bad_local {Ω : Type} [Fintype Ω] (A : QAdvMRGen m n w q k c a)
    (H : Ω → Fin m → Fin n) (f f' : Ω → Fin c → Fin a) (E : Ω → Finset (Fin c))
    (μ : Ω → ℝ≥0∞) (lam : ℝ≥0∞) (hμ : ∑ ω, μ ω ≤ 1)
    (hf : ∀ ω y, y ∉ E ω → f' ω y = f ω y)
    (hlam : ∀ (y : Fin c) (h₀ : Fin m → Fin n) (g : Fin c → Fin a),
      ∑ ω, μ ω * (if H ω = h₀ ∧ ∀ y', y' ≠ y → f ω y' = g y' then 1 else 0) *
          (if y ∈ E ω then 1 else 0) ≤
        lam * ∑ ω, μ ω * (if H ω = h₀ ∧ ∀ y', y' ≠ y → f ω y' = g y' then 1 else 0)) :
    absDiff (∑ ω, μ ω * prOutMRGen A (H ω) (f ω)) (∑ ω, μ ω * prOutMRGen A (H ω) (f' ω)) ≤
      k * lam := by
  set W : (Fin m → Fin n) → (Fin c → Fin a) → Fin c → ℝ := fun h g y =>
    badW1 (oracleQ m n w h) g {y} k q (fun i => (A.seg 0 i).toQComp)
      (fun j i => (Fin.tail A.seg j i).toQComp) A.rounds A.init.val with hWdef
  have hW : ∀ h g y, 0 ≤ W h g y := fun _ _ _ => badW1_nonneg _ _ _ _ _ _ _ _ _ A.init.psd
  have hWsum : ∀ h g, ∑ y, W h g y ≤ k := by
    intro h g
    have := sum_badW1_singleton_le (oracleQ m n w h) g k q (fun i => (A.seg 0 i).toQComp)
      (fun j i => (Fin.tail A.seg j i).toQComp) A.rounds A.init.val A.init.psd
    rwa [A.init.tr_one, Complex.one_re, mul_one] at this
  have hstep : ∀ ω, absDiff (prOutMRGen A (H ω) (f ω)) (prOutMRGen A (H ω) (f' ω)) ≤
      ∑ y, (if y ∈ E ω then 1 else 0) * ENNReal.ofReal (W (H ω) (f ω) y) := by
    intro ω
    refine (absDiff_prOutMRGen_le_badW1 A (H ω) (hf ω)).trans ?_
    refine (ENNReal.ofReal_le_ofReal
      (badW1_le_sum_singleton _ _ _ _ _ _ _ _ _ A.init.psd)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_sum_of_nonneg fun y _ => hW _ _ y, sum_mem_eq_sum_boole_mul]
  have hfib : ∀ y, ∑ ω, μ ω * (if y ∈ E ω then 1 else 0) * ENNReal.ofReal (W (H ω) (f ω) y) ≤
      lam * ∑ ω, μ ω * ENNReal.ofReal (W (H ω) (f ω) y) := by
    intro y
    have hκ : ∀ ω ω₀, ((H ω, fun y' => if y' = y then none else some (f ω y')) =
        (H ω₀, fun y' => if y' = y then none else some (f ω₀ y'))) ↔
        (H ω = H ω₀ ∧ ∀ y', y' ≠ y → f ω y' = f ω₀ y') := by
      simp only [Prod.mk.injEq, funext_iff]
      grind
    refine sum_mul_boole_mul_le_of_fiber
      (fun ω => (H ω, fun y' => if y' = y then none else some (f ω y'))) μ _
      (fun ω => y ∈ E ω) lam ?_ ?_
    · intro ω ω' he
      obtain ⟨h₁, h₂⟩ := (hκ ω ω').mp he
      simp only [hWdef, h₁]
      rw [badW1_congr _ (f := f ω') (f' := f ω) (fun y' hy' => h₂ y' (by simpa using hy'))]
    · intro ω₀
      simp only [hκ]
      exact hlam y (H ω₀) (f ω₀)
  calc absDiff (∑ ω, μ ω * prOutMRGen A (H ω) (f ω)) (∑ ω, μ ω * prOutMRGen A (H ω) (f' ω))
      ≤ ∑ ω, absDiff (μ ω * prOutMRGen A (H ω) (f ω)) (μ ω * prOutMRGen A (H ω) (f' ω)) :=
        absDiff_sum_le _ _
    _ ≤ ∑ ω, μ ω * absDiff (prOutMRGen A (H ω) (f ω)) (prOutMRGen A (H ω) (f' ω)) :=
        Finset.sum_le_sum fun ω _ => absDiff_mul_left_le _ _ _
    _ ≤ ∑ ω, μ ω * ∑ y, (if y ∈ E ω then 1 else 0) * ENNReal.ofReal (W (H ω) (f ω) y) := by
        gcongr with ω
        exact hstep ω
    _ = ∑ y, ∑ ω, μ ω * (if y ∈ E ω then 1 else 0) * ENNReal.ofReal (W (H ω) (f ω) y) := by
        simp only [Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
    _ ≤ ∑ y, lam * ∑ ω, μ ω * ENNReal.ofReal (W (H ω) (f ω) y) :=
        Finset.sum_le_sum fun y _ => hfib y
    _ = lam * ∑ ω, μ ω * ENNReal.ofReal (∑ y, W (H ω) (f ω) y) := by
        simp only [ENNReal.ofReal_sum_of_nonneg fun y _ => hW _ _ y, Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ lam * ∑ ω, μ ω * k := by
        gcongr with ω
        exact (ENNReal.ofReal_le_ofReal (hWsum _ _)).trans (by simp)
    _ = lam * ((∑ ω, μ ω) * k) := by rw [Finset.sum_mul]
    _ ≤ lam * (1 * k) := by gcongr
    _ = k * lam := by ring

end RoundsAdv

end CatCrypt.Quantum.QROM
