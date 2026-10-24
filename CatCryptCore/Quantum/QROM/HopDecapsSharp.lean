/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.HopDecaps

/-!
# The decapsulation hop localised at the queried ciphertexts

The simulated decapsulation function of `Quantum/QROM/HopDecaps.lean` and the
real one agree at every ciphertext except those carrying a message with a
decryption failure. This module isolates that set of ciphertexts, defines the
probability that a classical round's measurement lands in a set of register
values, and bounds the distance between two multi-round runs whose classical
functions agree outside a set by the total weight of the round measurements
inside it.

## Main definitions

* `badImage enc dec T` — the ciphertexts of the messages outside
  `Good enc dec (coinsOf T)`
* `badCts i`, `badFin i` — the same set at a KEM input, and its image in the
  round alphabet `Fin c`
* `roundProjS R S` — the projector `∑ y ∈ S, R.P y` of a classical round
* `preRoundChain A H f j` — the chain of segments and rounds before round `j`
* `roundGuessProb A H f S j` — the probability that round `j`'s measurement
  lands in `S`
* `roundWeightRe O f S k q₀ head tail R σ` — the total weight of the round
  measurements in `S` along the chain run with the classical function `f`
* `roundGuessRe O f S k q₀ head tail R j σ` — the weight of round `j` alone,
  by recursion on the chain

## Main results

* `simKeyAt_eq_keyAt_of_not_mem_badImage` — the table lookup and the
  decryption lookup agree off `badImage`
* `decapsSim_apply_eq_of_not_mem`, `decapsSim_eq_of_ne_bad` — the simulated and
  the real classical functions agree at a ciphertext outside `badCts`, and
  everywhere when no ciphertext is inside it
* `roundGuessProb_eq_sum` — `roundGuessProb A H f S j = ∑ y ∈ S, roundGuessProb A H f {y} j`
* `abs_acc_mrChain_sub_le` — two multi-round chains whose classical functions
  agree outside `S` differ, on every observable of the form "run the rest and
  accept", by at most `roundWeightRe`
* `absDiff_prOutMR_le_roundWeightRe`, `absDiff_prOutMR_le_sum_roundGuessProb` —
  the same bound on the output probabilities of a multi-round adversary, in the
  two forms of the weight
* `roundWeightRe_eq_sum_roundGuessRe`, `roundGuessRe_eq_trace`,
  `ofReal_roundWeightRe_eq_sum_roundGuessProb` — `roundWeightRe` is the sum
  over the rounds of the round measurement probabilities
* `hopD_sharp` — the decapsulation hop bounded by the averaged round-measurement
  probabilities at `badFin`

## The form of the bound

The two runs are compared round by round, and each round contributes its own
measurement weight with constant `1` and no factor from the query count. The bound
of `hopD_sharp` is the `kemSample`-average of a sum over the `k` decapsulation
rounds of the probability that the round's measurement lands in `badFin`, the event that the round queries a
ciphertext carrying a message with a decryption failure.

## References

* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.2
* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], §4.1
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.Measurement
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The ciphertexts of the failing messages -/

section BadImage

variable {M C Key Coin : Type} [Fintype M] [DecidableEq M] [DecidableEq C]

open scoped Classical in
/-- The ciphertexts of the messages that the decryption map does not recover
from their own ciphertext under the coins of `T`. -/
def badImage (enc : M → Coin → C) (dec : C → Option M) (T : M → Key × Coin) : Finset C :=
  (Finset.univ \ Good enc dec (coinsOf T)).image (encOf enc T)

open scoped Classical in
theorem mem_badImage_iff (enc : M → Coin → C) (dec : C → Option M) (T : M → Key × Coin)
    (c : C) :
    c ∈ badImage enc dec T ↔
      ∃ m, m ∉ Good enc dec (coinsOf T) ∧ encOf enc T m = c := by
  simp [badImage, Finset.mem_image, Finset.mem_sdiff]

open scoped Classical in
/-- Off the ciphertexts of the failing messages the table lookup agrees with the
lookup that reads the decryption map. -/
theorem simKeyAt_eq_keyAt_of_not_mem_badImage (enc : M → Coin → C) (dec : C → Option M)
    (T : M → Key × Coin) {c : C} (hc : c ∉ badImage enc dec T) :
    simKeyAt enc T c = keyAt enc dec T c := by
  by_cases hex : ∃ m, encOf enc T m = c
  · have hgood : hex.choose ∈ Good enc dec (coinsOf T) := by
      by_contra h
      exact hc ((mem_badImage_iff enc dec T c).2 ⟨hex.choose, h, hex.choose_spec⟩)
    calc simKeyAt enc T c = some (T hex.choose).1 := by rw [simKeyAt, dite_eq_left hex]
      _ = keyAt enc dec T (encOf enc T hex.choose) := (keyAt_encOf hgood).symm
      _ = keyAt enc dec T c := by rw [hex.choose_spec]
  · rw [simKeyAt_eq_none_of_not_mem_range hex,
      keyAt_eq_none_of_not_mem_image fun hmem => hex ?_]
    obtain ⟨m, _, hm⟩ := Finset.mem_image.1 hmem
    exact ⟨m, hm⟩

end BadImage

/-! ## The bad ciphertexts of a KEM input -/

section BadCts

variable {m₁ m₂ n c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype M] [DecidableEq M]
  [DecidableEq C] [Nonempty K] (P : Scheme PK SK M C R) (hpk : PK → Hash)
  (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n)
  (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

/-- The ciphertexts of the messages outside `kemGood i`. -/
def badCts (i : KEMInput PK SK Z M K m₁ m₂ n) : Finset C :=
  badImage (P.enc i.1.1) (P.dec i.1.2) (kemTab hpk eG eKR i)

/-- The bad ciphertexts of an input, in the round alphabet. -/
def badFin (i : KEMInput PK SK Z M K m₁ m₂ n) : Finset (Fin c) :=
  (badCts P hpk eG eKR i).image eC

omit [Nonempty K] in
theorem symm_not_mem_badCts_of_not_mem_badFin (i : KEMInput PK SK Z M K m₁ m₂ n) {x : Fin c}
    (hx : x ∉ badFin P hpk eG eKR eC i) : eC.symm x ∉ badCts P hpk eG eKR i := by
  intro hmem
  exact hx (Finset.mem_image.2 ⟨eC.symm x, hmem, eC.apply_symm_apply x⟩)

/-- At a ciphertext outside `badCts` the simulated and the real classical
functions of the rounds agree. -/
theorem decapsSim_apply_eq_of_not_mem (i : KEMInput PK SK Z M K m₁ m₂ n) (x : Fin c)
    (hx : eC.symm x ∉ badCts P hpk eG eKR i) :
    decapsSim P hpk eG eJ eKR eC eKa i x = kemDecaps P hpk eG eJ eKR eC eKa i x := by
  simp only [decapsSim, kemDecaps, decapsOracle]
  by_cases hc : eC.symm x = kemChal P hpk eG eKR i
  · rw [ite_eq_left hc, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc,
      simKeyAt_eq_keyAt_of_not_mem_badImage (P.enc i.1.1) (P.dec i.1.2)
        (kemTab hpk eG eKR i) hx,
      keyAt_getD_eq_decapsFixed]

/-- When no ciphertext is bad the simulated and the real classical functions of
the rounds coincide. -/
theorem decapsSim_eq_of_ne_bad (i : KEMInput PK SK Z M K m₁ m₂ n)
    (h : ∀ x : Fin c, eC.symm x ∉ badCts P hpk eG eKR i) :
    decapsSim P hpk eG eJ eKR eC eKa i = kemDecaps P hpk eG eJ eKR eC eKa i :=
  funext fun x => decapsSim_apply_eq_of_not_mem P hpk eG eJ eKR eC eKa i x (h x)

end BadCts

/-! ## The projector of a round on a set of outcomes -/

section RoundProj

variable {d c a : ℕ}

/-- The projector onto the outcomes of a round that lie in `S`. -/
def roundProjS (R : ClassicalRound d c a) (S : Finset (Fin c)) :
    Matrix (Fin d) (Fin d) ℂ := ∑ y ∈ S, R.P y

theorem roundProjS_conjTranspose (R : ClassicalRound d c a) (S : Finset (Fin c)) :
    (roundProjS R S)ᴴ = roundProjS R S := by
  unfold roundProjS
  rw [conjTranspose_sum]
  exact Finset.sum_congr rfl fun y _ => R.P_conjTranspose y

theorem roundProjS_mul_self (R : ClassicalRound d c a) (S : Finset (Fin c)) :
    roundProjS R S * roundProjS R S = roundProjS R S := by
  unfold roundProjS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finset.sum_eq_single y]
  · exact R.P_mul_self y
  · intro y' _ hy'; exact R.P_orth y y' (Ne.symm hy')
  · intro h; exact absurd hy h

theorem roundProjS_singleton (R : ClassicalRound d c a) (y : Fin c) :
    roundProjS R {y} = R.P y := by
  simp [roundProjS]

end RoundProj

/-! ## The probability that a round's measurement lands in a set -/

section RoundGuess

variable {m n w q k c a : ℕ} [NeZero n]

/-- The chain of segments and rounds run before round `j`. -/
def preRoundChain (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (j : Fin k) : QComp (m * n * w) Unit :=
  mrChain (oracleQ m n w H) f j q (A.seg 0)
    (fun i : Fin j => Fin.tail A.seg (Fin.castLE j.isLt.le i))
    (fun i : Fin j => A.rounds (Fin.castLE j.isLt.le i))

/-- The probability that the measurement of round `j` lands in `S`. -/
def roundGuessProb (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin c)) (j : Fin k) : ℝ≥0∞ :=
  prTrue_Q (QComp.qbind (preRoundChain A H f j) fun _ =>
    measProj (roundProjS (A.rounds j) S) (roundProjS_conjTranspose _ _)
      (roundProjS_mul_self _ _)) A.init

/-- `roundGuessProb` as the trace of the projector on the pre-round state. -/
theorem roundGuessProb_eq_trace (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin c)) (j : Fin k) :
    roundGuessProb A H f S j = ENNReal.ofReal
      (∑ y ∈ S, ((A.rounds j).P y *
        (preRoundChain A H f j).branch () A.init.val * (A.rounds j).P y).trace.re) := by
  unfold roundGuessProb prTrue_Q
  rw [qbind_unit_branch, measProj_branch_true, roundProjS_conjTranspose,
    trace_proj_mul_mul_proj (roundProjS_mul_self _ _)]
  congr 1
  have hcyc : ∀ y : Fin c, ((A.rounds j).P y *
      (preRoundChain A H f j).branch () A.init.val * (A.rounds j).P y).trace =
      ((A.rounds j).P y * (preRoundChain A H f j).branch () A.init.val).trace := fun y =>
    trace_proj_mul_mul_proj ((A.rounds j).P_mul_self y) _
  simp only [hcyc]
  rw [roundProjS, Finset.sum_mul, trace_sum]
  exact (map_sum Complex.reAddGroupHom _ _)

/-- The measurement weight of a round at a set is the sum of its weights at the
singletons. -/
theorem roundGuessProb_eq_sum (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin c)) (j : Fin k) :
    roundGuessProb A H f S j = ∑ y ∈ S, roundGuessProb A H f {y} j := by
  have hpsd : ((preRoundChain A H f j).branch () A.init.val).PosSemidef :=
    (preRoundChain A H f j).branch_psd () A.init.val A.init.psd
  have hnn : ∀ y : Fin c, 0 ≤ ((A.rounds j).P y *
      (preRoundChain A H f j).branch () A.init.val * (A.rounds j).P y).trace.re := by
    intro y
    refine trace_re_nonneg_of_psd ?_
    have h := hpsd.mul_mul_conjTranspose_same ((A.rounds j).P y)
    rwa [(A.rounds j).P_conjTranspose y] at h
  rw [roundGuessProb_eq_trace, ENNReal.ofReal_sum_of_nonneg fun y _ => hnn y]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [roundGuessProb_eq_trace]
  simp

end RoundGuess

/-! ## The weight of the round measurements along a chain -/

section Weight

variable {d c a q : ℕ}

/-- The total weight of the round measurements landing in `S`, along the chain
run with the classical function `f` from the state `σ`. -/
def roundWeightRe (O : QComp d Unit) (f : Fin c → Fin a) (S : Finset (Fin c)) :
    (k : ℕ) → (q₀ : ℕ) → (Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → ClassicalRound d c a) → Matrix (Fin d) (Fin d) ℂ → ℝ
  | 0, _, _, _, _ => fun _ => 0
  | k + 1, q₀, head, tail, R => fun σ =>
      (∑ y ∈ S, ((R 0).P y * (oracleChain O q₀ head).branch () σ * (R 0).P y).trace.re) +
        roundWeightRe O f S k q (tail 0) (Fin.tail tail) (Fin.tail R)
          ((roundU (R 0) f).branch () ((oracleChain O q₀ head).branch () σ))

theorem roundWeightRe_add (O : QComp d Unit) (f : Fin c → Fin a) (S : Finset (Fin c)) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (σ τ : Matrix (Fin d) (Fin d) ℂ),
      roundWeightRe O f S k q₀ head tail R (σ + τ) =
        roundWeightRe O f S k q₀ head tail R σ + roundWeightRe O f S k q₀ head tail R τ := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _; simp [roundWeightRe]
  | succ k ih =>
    intro q₀ head tail R σ τ
    show (∑ y ∈ S, _) + _ = ((∑ y ∈ S, _) + _) + ((∑ y ∈ S, _) + _)
    have hsum : ∀ (x z : Matrix (Fin d) (Fin d) ℂ),
        (∑ y ∈ S, ((R 0).P y * (x + z) * (R 0).P y).trace.re) =
          (∑ y ∈ S, ((R 0).P y * x * (R 0).P y).trace.re) +
            ∑ y ∈ S, ((R 0).P y * z * (R 0).P y).trace.re := by
      intro x z
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Matrix.mul_add, Matrix.add_mul, trace_add, Complex.add_re]
    rw [map_add, map_add, hsum, ih]
    ring

theorem roundWeightRe_zero (O : QComp d Unit) (f : Fin c → Fin a) (S : Finset (Fin c))
    (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin k → ClassicalRound d c a) :
    roundWeightRe O f S k q₀ head tail R 0 = 0 := by
  have h := roundWeightRe_add O f S k q₀ head tail R 0 0
  rw [add_zero] at h
  linarith

theorem roundWeightRe_sum {ι : Type} (O : QComp d Unit) (f : Fin c → Fin a)
    (S : Finset (Fin c)) (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (R : Fin k → ClassicalRound d c a) (s : Finset ι)
    (σ : ι → Matrix (Fin d) (Fin d) ℂ) :
    roundWeightRe O f S k q₀ head tail R (∑ i ∈ s, σ i) =
      ∑ i ∈ s, roundWeightRe O f S k q₀ head tail R (σ i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [roundWeightRe_zero]
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, roundWeightRe_add, ih, Finset.sum_insert hx]

theorem roundWeightRe_nonneg (O : QComp d Unit) (f : Fin c → Fin a) (S : Finset (Fin c)) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ), σ.PosSemidef →
      0 ≤ roundWeightRe O f S k q₀ head tail R σ := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _; simp [roundWeightRe]
  | succ k ih =>
    intro q₀ head tail R σ hσ
    have hσ' : ((oracleChain O q₀ head).branch () σ).PosSemidef :=
      (oracleChain O q₀ head).branch_psd () σ hσ
    refine add_nonneg (Finset.sum_nonneg fun y _ => ?_) (ih _ _ _ _ _ ?_)
    · refine trace_re_nonneg_of_psd ?_
      have h := hσ'.mul_mul_conjTranspose_same ((R 0).P y)
      rwa [(R 0).P_conjTranspose y] at h
    · exact (roundU (R 0) f).branch_psd () _ hσ'

/-- The weight of the measurement of round `j` landing in `S`, on the state the
chain reaches before that round; `0` when there is no round `j`. -/
def roundGuessRe (O : QComp d Unit) (f : Fin c → Fin a) (S : Finset (Fin c)) :
    (k : ℕ) → (q₀ : ℕ) → (Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) →
      (Fin k → ClassicalRound d c a) → ℕ → Matrix (Fin d) (Fin d) ℂ → ℝ
  | 0, _, _, _, _, _ => fun _ => 0
  | _ + 1, q₀, head, _, R, 0 => fun σ =>
      ∑ y ∈ S, ((R 0).P y * (oracleChain O q₀ head).branch () σ * (R 0).P y).trace.re
  | k + 1, q₀, head, tail, R, j + 1 => fun σ =>
      roundGuessRe O f S k q (tail 0) (Fin.tail tail) (Fin.tail R) j
        ((roundU (R 0) f).branch () ((oracleChain O q₀ head).branch () σ))

theorem roundWeightRe_eq_sum_roundGuessRe (O : QComp d Unit) (f : Fin c → Fin a)
    (S : Finset (Fin c)) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ),
      roundWeightRe O f S k q₀ head tail R σ =
        ∑ j ∈ Finset.range k, roundGuessRe O f S k q₀ head tail R j σ := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _; simp [roundWeightRe]
  | succ k ih =>
    intro q₀ head tail R σ
    rw [Finset.sum_range_succ']
    show (∑ y ∈ S, _) + roundWeightRe O f S k q (tail 0) (Fin.tail tail) (Fin.tail R) _ = _
    rw [ih]
    rw [add_comm]
    rfl

theorem roundGuessRe_nonneg (O : QComp d Unit) (f : Fin c → Fin a) (S : Finset (Fin c)) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (j : ℕ) (σ : Matrix (Fin d) (Fin d) ℂ),
      σ.PosSemidef → 0 ≤ roundGuessRe O f S k q₀ head tail R j σ := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _; simp [roundGuessRe]
  | succ k ih =>
    intro q₀ head tail R j σ hσ
    have hσ' : ((oracleChain O q₀ head).branch () σ).PosSemidef :=
      (oracleChain O q₀ head).branch_psd () σ hσ
    cases j with
    | zero =>
      refine Finset.sum_nonneg fun y _ => trace_re_nonneg_of_psd ?_
      have h := hσ'.mul_mul_conjTranspose_same ((R 0).P y)
      rwa [(R 0).P_conjTranspose y] at h
    | succ j => exact ih _ _ _ _ _ _ ((roundU (R 0) f).branch_psd () _ hσ')

/-- `roundGuessRe` at a round index is the weight of that round's projectors on
the state the chain reaches before it. -/
theorem roundGuessRe_eq_trace (O : QComp d Unit) (f : Fin c → Fin a) (S : Finset (Fin c)) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (j : Fin k) (σ : Matrix (Fin d) (Fin d) ℂ),
      roundGuessRe O f S k q₀ head tail R j σ =
        ∑ y ∈ S, ((R j).P y * (mrChain O f j q₀ head
          (fun i : Fin (j : ℕ) => tail (Fin.castLE j.isLt.le i))
          (fun i : Fin (j : ℕ) => R (Fin.castLE j.isLt.le i))).branch () σ *
            (R j).P y).trace.re := by
  intro k
  induction k with
  | zero => intro _ _ _ _ j; exact absurd j.isLt (by omega)
  | succ k ih =>
    intro q₀ head tail R j σ
    refine Fin.cases ?_ ?_ j
    · rfl
    · intro i
      show roundGuessRe O f S k q (tail 0) (Fin.tail tail) (Fin.tail R) i _ = _
      rw [ih]
      have hT : (fun i'' : Fin (i : ℕ) => Fin.tail tail (Fin.castLE i.isLt.le i'')) =
          Fin.tail (fun i' : Fin ((i.succ : Fin (k + 1)) : ℕ) =>
            tail (Fin.castLE (i.succ : Fin (k + 1)).isLt.le i')) := by
        funext i''
        show tail _ = tail _
        congr 1
      have hR : (fun i'' : Fin (i : ℕ) => Fin.tail R (Fin.castLE i.isLt.le i'')) =
          Fin.tail (fun i' : Fin ((i.succ : Fin (k + 1)) : ℕ) =>
            R (Fin.castLE (i.succ : Fin (k + 1)).isLt.le i')) := by
        funext i''
        show R _ = R _
        congr 1
      have hstep : ∀ (T' : Fin ((i.succ : Fin (k + 1)) : ℕ) → Fin (q + 1) →
            Matrix.unitaryGroup (Fin d) ℂ)
          (R' : Fin ((i.succ : Fin (k + 1)) : ℕ) → ClassicalRound d c a),
          (mrChain O f ((i.succ : Fin (k + 1)) : ℕ) q₀ head T' R').branch () σ =
            (mrChain O f (i : ℕ) q (T' ⟨0, Nat.succ_pos _⟩) (Fin.tail T') (Fin.tail R')).branch ()
              ((roundU (R' ⟨0, Nat.succ_pos _⟩) f).branch ()
                ((oracleChain O q₀ head).branch () σ)) := by
        intro T' R'
        show (QComp.qbind (oracleChain O q₀ head) fun _ =>
          QComp.qbind (roundU (R' ⟨0, Nat.succ_pos _⟩) f) fun _ =>
            mrChain O f (i : ℕ) q (T' ⟨0, Nat.succ_pos _⟩) (Fin.tail T')
              (Fin.tail R')).branch () σ = _
        rw [qbind_unit_branch, qbind_unit_branch]
      rw [hT, hR, hstep]
      rfl

end Weight

/-! ## Two chains whose classical functions agree outside a set -/

section Sharp

variable {d c a q : ℕ}

/-- Two multi-round chains whose classical functions agree outside `S` differ,
on the acceptance probability of any continuation, by at most the total weight
of the round measurements inside `S`. -/
theorem abs_acc_mrChain_sub_le (O : QComp d Unit) (Rest : QComp d Bool)
    (f f' : Fin c → Fin a) (S : Finset (Fin c)) (hff' : ∀ y, y ∉ S → f y = f' y) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (σ : Matrix (Fin d) (Fin d) ℂ), σ.PosSemidef →
      |(Rest.branch true ((mrChain O f k q₀ head tail R).branch () σ)).trace.re -
          (Rest.branch true ((mrChain O f' k q₀ head tail R).branch () σ)).trace.re| ≤
        roundWeightRe O f S k q₀ head tail R σ := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _; simp [mrChain, roundWeightRe]
  | succ k ih =>
    intro q₀ head tail R σ hσ
    have hσ' : ((oracleChain O q₀ head).branch () σ).PosSemidef :=
      (oracleChain O q₀ head).branch_psd () σ hσ
    set σ' := (oracleChain O q₀ head).branch () σ with hσ'def
    set Tail : (Fin c → Fin a) → QComp d Unit := fun g =>
      mrChain O g k q (tail 0) (Fin.tail tail) (Fin.tail R) with hTail
    set K : (Fin c → Fin a) → Fin c → Matrix (Fin d) (Fin d) ℂ := fun g y =>
      ((R 0).ans (g y) : Matrix (Fin d) (Fin d) ℂ) * (R 0).P y with hK
    set τ : (Fin c → Fin a) → Fin c → Matrix (Fin d) (Fin d) ℂ := fun g y =>
      K g y * σ' * (K g y)ᴴ with hτ
    set acc : (Fin c → Fin a) → Fin c → ℝ := fun g y =>
      (Rest.branch true ((Tail g).branch () (τ g y))).trace.re with hacc
    have hτpsd : ∀ g y, (τ g y).PosSemidef := fun g y => hσ'.mul_mul_conjTranspose_same _
    have hsplit : ∀ g : Fin c → Fin a,
        (Rest.branch true ((mrChain O g (k + 1) q₀ head tail R).branch () σ)).trace.re =
          ∑ y, acc g y := by
      intro g
      have hbr : (mrChain O g (k + 1) q₀ head tail R).branch () σ =
          (Tail g).branch () ((roundU (R 0) g).branch () σ') := by
        show (QComp.qbind (oracleChain O q₀ head) fun _ =>
          QComp.qbind (roundU (R 0) g) fun _ => Tail g).branch () σ = _
        rw [qbind_unit_branch, qbind_unit_branch]
      rw [hbr, roundU_branch]
      have hsum : (roundU (R 0) g).branch () σ' = ∑ y, τ g y := by
        rw [roundU_branch]
      rw [← hsum, hsum, map_sum, map_sum, trace_sum]
      exact map_sum Complex.reAddGroupHom _ _
    rw [hsplit f, hsplit f', ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hw : ∀ y : Fin c, (τ f y).trace.re = ((R 0).P y * σ' * (R 0).P y).trace.re := by
      intro y
      have hcong : τ f y = ((R 0).ans (f y) : Matrix (Fin d) (Fin d) ℂ) *
          ((R 0).P y * σ' * (R 0).P y) *
          ((R 0).ans (f y) : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
        simp only [hτ, hK, conjTranspose_mul, (R 0).P_conjTranspose]
        simp only [Matrix.mul_assoc]
      rw [hcong, trace_mul_mul_conjTranspose_of_mem_unitaryGroup ((R 0).ans (f y)).prop]
    have hbound : ∀ (g : Fin c → Fin a) (y : Fin c),
        0 ≤ acc g y ∧ acc g y ≤ (τ g y).trace.re := by
      intro g y
      refine ⟨trace_re_nonneg_of_psd (Rest.branch_psd true _ ((Tail g).branch_psd () _
        (hτpsd g y))), ?_⟩
      exact (branch_trace_re_le Rest true _ ((Tail g).branch_psd () _ (hτpsd g y))).trans
        (branch_trace_re_le (Tail g) () _ (hτpsd g y))
    have hterm : ∀ y : Fin c, |acc f y - acc f' y| ≤
        (if y ∈ S then ((R 0).P y * σ' * (R 0).P y).trace.re
          else roundWeightRe O f S k q (tail 0) (Fin.tail tail) (Fin.tail R) (τ f y)) := by
      intro y
      by_cases hy : y ∈ S
      · rw [ite_eq_left hy]
        have hf := hbound f y
        have hf' := hbound f' y
        have hw' : (τ f' y).trace.re = ((R 0).P y * σ' * (R 0).P y).trace.re := by
          have hcong : τ f' y = ((R 0).ans (f' y) : Matrix (Fin d) (Fin d) ℂ) *
              ((R 0).P y * σ' * (R 0).P y) *
              ((R 0).ans (f' y) : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
            simp only [hτ, hK, conjTranspose_mul, (R 0).P_conjTranspose]
            simp only [Matrix.mul_assoc]
          rw [hcong, trace_mul_mul_conjTranspose_of_mem_unitaryGroup ((R 0).ans (f' y)).prop]
        rw [hw] at hf
        rw [hw'] at hf'
        rw [abs_le]
        constructor <;> linarith [hf.1, hf.2, hf'.1, hf'.2]
      · rw [ite_eq_right hy]
        have hτeq : τ f' y = τ f y := by simp only [hτ, hK, hff' y hy]
        have := ih q (tail 0) (Fin.tail tail) (Fin.tail R) (τ f y) (hτpsd f y)
        simp only [hacc, hTail, hτeq]
        exact this
    refine (Finset.sum_le_sum fun y _ => hterm y).trans ?_
    have hS : Finset.univ.filter (fun y : Fin c => y ∈ S) = S := by
      ext y; simp
    have hSc : Finset.univ.filter (fun y : Fin c => y ∉ S) = Finset.univ \ S := by
      ext y; simp
    rw [Finset.sum_ite, hS, hSc]
    show _ ≤ (∑ y ∈ S, ((R 0).P y * σ' * (R 0).P y).trace.re) +
      roundWeightRe O f S k q (tail 0) (Fin.tail tail) (Fin.tail R)
        ((roundU (R 0) f).branch () σ')
    gcongr
    rw [← roundWeightRe_sum]
    have hcompl : ((roundU (R 0) f).branch () σ') =
        (∑ y ∈ Finset.univ \ S, τ f y) + ∑ y ∈ S, τ f y := by
      rw [Finset.sum_sdiff (Finset.subset_univ S), roundU_branch]
    rw [hcompl, roundWeightRe_add]
    have hnn : 0 ≤ roundWeightRe O f S k q (tail 0) (Fin.tail tail) (Fin.tail R)
        (∑ y ∈ S, τ f y) :=
      roundWeightRe_nonneg O f S k q (tail 0) (Fin.tail tail) (Fin.tail R) _
        (Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
          Matrix.PosSemidef.zero fun y _ => hτpsd f y)
    linarith

end Sharp

/-! ## The bound on the output probability of a multi-round adversary -/

section MRBound

variable {m n w q k c a : ℕ} [NeZero n]

theorem prOutMR_eq_ofReal_acc (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) :
    prOutMR A H f = ENNReal.ofReal
      (A.measure.branch true ((mrChain (oracleQ m n w H) f k q (A.seg 0) (Fin.tail A.seg)
        A.rounds).branch () A.init.val)).trace.re := by
  unfold prOutMR prTrue_Q runMR
  rw [qbind_unit_branch]

/-- Two runs of a multi-round adversary whose classical functions agree outside
`S` differ by at most the total weight of the round measurements inside `S`. -/
theorem absDiff_prOutMR_le_roundWeightRe (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f f' : Fin c → Fin a) (S : Finset (Fin c)) (hff' : ∀ y, y ∉ S → f y = f' y) :
    absDiff (prOutMR A H f) (prOutMR A H f') ≤
      ENNReal.ofReal (roundWeightRe (oracleQ m n w H) f S k q (A.seg 0) (Fin.tail A.seg)
        A.rounds A.init.val) := by
  have hnn : ∀ g : Fin c → Fin a, 0 ≤
      (A.measure.branch true ((mrChain (oracleQ m n w H) g k q (A.seg 0) (Fin.tail A.seg)
        A.rounds).branch () A.init.val)).trace.re := fun g =>
    trace_re_nonneg_of_psd (A.measure.branch_psd true _
      ((mrChain (oracleQ m n w H) g k q (A.seg 0) (Fin.tail A.seg) A.rounds).branch_psd ()
        _ A.init.psd))
  rw [prOutMR_eq_ofReal_acc, prOutMR_eq_ofReal_acc]
  refine (absDiff_ofReal_le (hnn f) (hnn f')).trans (ENNReal.ofReal_le_ofReal ?_)
  exact abs_acc_mrChain_sub_le (oracleQ m n w H) A.measure f f' S hff' k q (A.seg 0)
    (Fin.tail A.seg) A.rounds A.init.val A.init.psd

/-- The total round weight is the sum over the rounds of the measurement
probabilities. -/
theorem ofReal_roundWeightRe_eq_sum_roundGuessProb (A : QAdvMR m n w q k c a)
    (H : Fin m → Fin n) (f : Fin c → Fin a) (S : Finset (Fin c)) :
    ENNReal.ofReal (roundWeightRe (oracleQ m n w H) f S k q (A.seg 0) (Fin.tail A.seg)
        A.rounds A.init.val) =
      ∑ j : Fin k, roundGuessProb A H f S j := by
  rw [roundWeightRe_eq_sum_roundGuessRe, ENNReal.ofReal_sum_of_nonneg fun j _ =>
    roundGuessRe_nonneg (oracleQ m n w H) f S k q (A.seg 0) (Fin.tail A.seg) A.rounds j
      A.init.val A.init.psd,
    ← Fin.sum_univ_eq_sum_range fun j => ENNReal.ofReal
      (roundGuessRe (oracleQ m n w H) f S k q (A.seg 0) (Fin.tail A.seg) A.rounds j A.init.val)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [roundGuessRe_eq_trace, roundGuessProb_eq_trace]
  rfl

/-- Two runs of a multi-round adversary whose classical functions agree outside
`S` differ by at most the summed measurement probabilities of the rounds at
`S`. -/
theorem absDiff_prOutMR_le_sum_roundGuessProb (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f f' : Fin c → Fin a) (S : Finset (Fin c)) (hff' : ∀ y, y ∉ S → f y = f' y) :
    absDiff (prOutMR A H f) (prOutMR A H f') ≤ ∑ j : Fin k, roundGuessProb A H f S j := by
  rw [← ofReal_roundWeightRe_eq_sum_roundGuessProb]
  exact absDiff_prOutMR_le_roundWeightRe A H f f' S hff'

end MRBound

/-! ## The decapsulation hop at the queried ciphertexts -/

section HopSharp

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [Fintype K] [DecidableEq K]
  [Nonempty K] [Fintype R] [DecidableEq R] [Nonempty R] [Fintype C] [DecidableEq C] [NeZero n]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

omit [Nonempty M] [Nonempty Z] [DecidableEq K] [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] in
/-- The decapsulation hop localised at the rounds: the two games differ by at
most the summed probabilities that a round's measurement lands on a bad
ciphertext. -/
theorem hopD_sharp (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    absDiff (prWinKEM P hpk eG eJ eKR eC eKa A b)
        (prWinKEMSim P hpk eG eJ eKR eC eKa A b) ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
        ∑ j : Fin k, roundGuessProb (A.run i.1.1 (kemChal P hpk eG eKR i)
          (kemKey hpk eG eKR i b)) (kemOracle i) (kemDecaps P hpk eG eJ eKR eC eKa i)
            (badFin P hpk eG eKR eC i) j := by
  refine le_trans (absDiff_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  refine le_trans (absDiff_mul_left_le _ _ _) ?_
  gcongr
  refine absDiff_prOutMR_le_sum_roundGuessProb _ _ _ _ _ fun y hy => ?_
  exact (decapsSim_apply_eq_of_not_mem P hpk eG eJ eKR eC eKa i y
    (symm_not_mem_badCts_of_not_mem_badFin P hpk eG eKR eC i hy)).symm

end HopSharp

end CatCrypt.Quantum.QROM
