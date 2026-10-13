/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.QOwcpaAux

/-!
# A quantum IND-CPA game with oracle access, and one-wayness from it

The one-wayness game `qOwcpaAux` of `Quantum/QROM/QOwcpaAux.lean` gives the
adversary the public key, the challenge ciphertext and superposition access to
the challenger's tables. This module states the IND-CPA game over the same
oracles and bounds the one-wayness winning probability by the IND-CPA advantage
of a reduction that keeps its oracle calls.

## Main definitions

* `truncAdv A j F` — the adversary that runs `A` up to and including `U_j`,
  with its first `j` oracle calls kept, and measures the projector `F`
* `auxTabAvg f` — the uniform average of `f` over the coins and the tables
  `G`, `J`, `Hq`, `T` and the seed `z`, in the order of `qOwcpaAux`
* `QIndAuxAdv ι` — an adversary of the IND-CPA game: two messages from its
  public key and coins, and from the public key, the challenge ciphertext, the
  value of `Hq` at it and its coins, a multi-round adversary, a stop index and
  a final projector
* `qIndcpaAuxPr P … D b` — the probability that `D` outputs `1` when the
  challenge ciphertext encrypts message `b`
* `qIndcpaAux P … D` — the advantage `|Pr[1 | b = 1] - Pr[1 | b = 0]|`
* `msgSet eG m` — the oracle points whose message is `m`
* `indRed B` — the reduction: coins two messages, runs the one-wayness
  adversary `B` and measures whether the message of the query register is the
  second message
* `corrErr P` — the weight of the key pairs, messages and coins at which the
  decryption of the encryption differs from the message

## Main results

* `sum_prOut_queryPrefix_fiber_le_one` — the acceptance probabilities of the
  prefixes at the fibres of a function on the query register sum to at most one
* `qOwcpaAux_le_qIndcpaAux` —
  `qOwcpaAux B ≤ qIndcpaAux (indRed B) + |M|⁻¹ + corrErr P`

## Scope

The code of `indRed B` is the code of `B`, two uniform classical message draws
and one projector on the query register, the preimage of the second message
under the message decoding of the `G`-index. It draws no table and computes no
measurement distribution; its cost is that of `B`. The first stage of the
reduction, the choice of the two messages, has classical state only. The
IND-CPA adversary receives the same auxiliary oracles as in `qOwcpaAux`: the
merged oracle `auxOracle`, the decapsulation answers `decapsHq Hq c*` and the
value `Hq c*`.

## References

* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §2
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Truncated adversaries with a final projector -/

section Trunc

variable {m n w q : ℕ}

/-- The adversary that runs `A` up to and including `U_j`, with its first `j`
oracle calls kept as oracle calls, and measures the projector `F`. -/
def truncAdv (A : QAdv m n w q) (j : Fin q) (F : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ)
    (hH : Fᴴ = F) (hI : F * F = F) : QAdv m n w j where
  U i := A.U (Fin.castLE (Nat.succ_le_succ j.isLt.le) i)
  init := A.init
  final := F
  final_conjTranspose := hH
  final_mul_self := hI

/-- `queryPrefix` is `truncAdv` at the projector `projS S`. -/
theorem truncAdv_projS (A : QAdv m n w q) (S : Finset (Fin m)) (j : Fin q) :
    truncAdv A j (projS m n w S) (projS_conjTranspose m n w S) (projS_mul_self m n w S) =
      queryPrefix A S j := rfl

/-- The projectors onto the fibres of `g` sum to the projector onto the whole
query register. -/
theorem sum_projS_fiber {β : Type} [Fintype β] [DecidableEq β] (g : Fin m → β) :
    ∑ b, projS m n w (Finset.univ.filter fun t => g t = b) = projS m n w Finset.univ := by
  simp only [projS_eq_diagonal]
  ext k l
  rw [Matrix.sum_apply]
  by_cases h : k = l <;> simp [h, indS]

variable [NeZero n]

/-- The state of `A` against `H` before query `j`, after `U_j`. -/
def prefixState (A : QAdv m n w q) (H : Fin m → Fin n) (j : Fin q) :
    Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ :=
  (oracleChain (oracleQ m n w H) j fun i => A.U (Fin.castLE (Nat.succ_le_succ j.isLt.le) i)).branch
    () A.init.val

/-- The acceptance probability of `queryPrefix A S j` is the trace of `projS S`
against `prefixState A H j`. -/
theorem prOut_queryPrefix_eq_trace (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    (j : Fin q) :
    prOut (queryPrefix A S j) H =
      ENNReal.ofReal (projS m n w S * prefixState A H j).trace.re := by
  rw [prOut_eq_trace_scChain_empty, scChain_empty_branch_false]
  rfl

/-- The trace of `projS S` against `prefixState A H j` has non-negative real
part. -/
theorem trace_projS_prefixState_nonneg (A : QAdv m n w q) (H : Fin m → Fin n)
    (S : Finset (Fin m)) (j : Fin q) :
    0 ≤ (projS m n w S * prefixState A H j).trace.re := by
  have hσ := (oracleChain (oracleQ m n w H) j fun i =>
    A.U (Fin.castLE (Nat.succ_le_succ j.isLt.le) i)).branch_psd () A.init.val A.init.psd
  have h := trace_re_nonneg_of_psd
    ((measProj _ (projS_conjTranspose m n w S) (projS_mul_self m n w S)).branch_psd true _ hσ)
  rwa [measProj_branch_true, projS_conjTranspose,
    trace_proj_mul_mul_proj (projS_mul_self m n w S)] at h

/-- The acceptance probabilities of the prefixes at the fibres of a function on
the query register sum to at most one. -/
theorem sum_prOut_queryPrefix_fiber_le_one {β : Type} [Fintype β] [DecidableEq β]
    (A : QAdv m n w q) (H : Fin m → Fin n) (j : Fin q) (g : Fin m → β) :
    ∑ b, prOut (queryPrefix A (Finset.univ.filter fun t => g t = b) j) H ≤ 1 := by
  simp only [prOut_queryPrefix_eq_trace]
  rw [← ENNReal.ofReal_sum_of_nonneg fun b _ => trace_projS_prefixState_nonneg A H _ j]
  have hsum : ∑ b, (projS m n w (Finset.univ.filter fun t => g t = b) *
      prefixState A H j).trace.re = (projS m n w Finset.univ * prefixState A H j).trace.re := by
    rw [← Complex.re_sum, ← trace_sum, ← Finset.sum_mul, sum_projS_fiber]
  rw [hsum, ← prOut_queryPrefix_eq_trace]
  exact prTrue_Q_le_one _ _

end Trunc

/-! ## The average over the coins and the tables -/

section TabAvg

variable {m₁ m₂ n : ℕ} {C K R Z : Type} [Fintype C] [DecidableEq C] [Fintype K] [Fintype R]
  [Fintype Z]

/-- The uniform average of `f` over the coins, the seed and the tables `G`, `J`,
`Hq`, `T`, nested in the order of `qOwcpaAux`. -/
def auxTabAvg
    (f : R → Z → (Fin m₁ → Fin n) → (Fin m₂ → Fin n) → (C → K) → (C → Fin n) → ℝ≥0∞) :
    ℝ≥0∞ :=
  ∑ r : R, (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ z : Z, (Fintype.card Z : ℝ≥0∞)⁻¹ *
    ∑ G : Fin m₁ → Fin n, (Fintype.card (Fin m₁ → Fin n) : ℝ≥0∞)⁻¹ *
      ∑ J : Fin m₂ → Fin n, (Fintype.card (Fin m₂ → Fin n) : ℝ≥0∞)⁻¹ *
        ∑ Hq : C → K, (Fintype.card (C → K) : ℝ≥0∞)⁻¹ *
          ∑ T : C → Fin n, (Fintype.card (C → Fin n) : ℝ≥0∞)⁻¹ * f r z G J Hq T

/-- `auxTabAvg` is monotone. -/
theorem auxTabAvg_mono
    {f g : R → Z → (Fin m₁ → Fin n) → (Fin m₂ → Fin n) → (C → K) → (C → Fin n) → ℝ≥0∞}
    (h : ∀ r z G J Hq T, f r z G J Hq T ≤ g r z G J Hq T) : auxTabAvg f ≤ auxTabAvg g := by
  unfold auxTabAvg
  gcongr with r _ z _ G _ J _ Hq _ T _
  exact h r z G J Hq T

/-- `auxTabAvg` is additive. -/
theorem auxTabAvg_add
    (f g : R → Z → (Fin m₁ → Fin n) → (Fin m₂ → Fin n) → (C → K) → (C → Fin n) → ℝ≥0∞) :
    auxTabAvg (fun r z G J Hq T => f r z G J Hq T + g r z G J Hq T) =
      auxTabAvg f + auxTabAvg g := by
  simp only [auxTabAvg, mul_add, Finset.sum_add_distrib]

/-- `auxTabAvg` commutes with a constant factor. -/
theorem auxTabAvg_mul_left (s : ℝ≥0∞)
    (f : R → Z → (Fin m₁ → Fin n) → (Fin m₂ → Fin n) → (C → K) → (C → Fin n) → ℝ≥0∞) :
    auxTabAvg (fun r z G J Hq T => s * f r z G J Hq T) = s * auxTabAvg f := by
  simp only [auxTabAvg, Finset.mul_sum, mul_left_comm s]

/-- `auxTabAvg` commutes with a finite sum. -/
theorem auxTabAvg_sum {ι : Type} [Fintype ι]
    (f : ι → R → Z → (Fin m₁ → Fin n) → (Fin m₂ → Fin n) → (C → K) → (C → Fin n) → ℝ≥0∞) :
    auxTabAvg (fun r z G J Hq T => ∑ i, f i r z G J Hq T) = ∑ i, auxTabAvg (f i) := by
  simp only [auxTabAvg, Finset.mul_sum]
  symm
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => ?_)
  exact Finset.sum_comm

/-- The uniform average of a constant is the constant. -/
theorem sum_inv_mul_const {α : Type} [Fintype α] [Nonempty α] (s : ℝ≥0∞) :
    ∑ _x : α, (Fintype.card α : ℝ≥0∞)⁻¹ * s = s := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _), one_mul]

variable [Nonempty Z] [Nonempty K] [NeZero n]

/-- The average of a function of the coins alone is its average over the coins. -/
theorem auxTabAvg_of_coins (g : R → ℝ≥0∞) :
    auxTabAvg (m₁ := m₁) (m₂ := m₂) (n := n) (C := C) (K := K) (Z := Z)
        (fun r _ _ _ _ _ => g r) = ∑ r, (Fintype.card R : ℝ≥0∞)⁻¹ * g r := by
  simp only [auxTabAvg, sum_inv_mul_const]

/-- The average of a constant is the constant. -/
theorem auxTabAvg_const [Nonempty R] (s : ℝ≥0∞) :
    auxTabAvg (m₁ := m₁) (m₂ := m₂) (n := n) (C := C) (K := K) (R := R) (Z := Z)
        (fun _ _ _ _ _ _ => s) = s := by
  simp only [auxTabAvg, sum_inv_mul_const]

end TabAvg

/-! ## The game -/

/-- An adversary of `qIndcpaAux` with coins in `ι`: two messages from the public
key and its coins, and from the public key, the challenge ciphertext, a key and
its coins, a multi-round adversary, the index of the query before which it
stops, and the projector whose outcome `true` is the output `1`. -/
structure QIndAuxAdv (ι : Type) (m n W q k c a : ℕ) (PK C K M : Type) where
  /-- The two messages. -/
  msgs : PK → ι → M × M
  /-- The multi-round adversary it runs. -/
  prog : PK → C → K → ι → QAdvMR m n W q k c a
  /-- The query index at which the run stops. -/
  stop : PK → C → K → ι → Fin (flatQ q k q)
  /-- The projector of the final measurement. -/
  final : PK → C → K → ι → Matrix (Fin (m * n * ancW c k W)) (Fin (m * n * ancW c k W)) ℂ
  final_conjTranspose : ∀ pk cst h x, (final pk cst h x)ᴴ = final pk cst h x
  final_mul_self : ∀ pk cst h x, final pk cst h x * final pk cst h x = final pk cst h x

section Game

variable {m₁ m₂ n W q k c a : ℕ} {PK SK M C R K Hash Z ι : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [DecidableEq Z] [Fintype K] [Nonempty K]
  [Fintype R] [Fintype C] [DecidableEq C] [DecidableEq Hash] [Fintype ι]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c]

/-- The probability that `D` with coins `x` outputs `1` at a public key, a
challenge ciphertext and the challenger's tables: `D` receives `pk`, `cst` and
`Hq cst`, runs against `auxOracle` with decapsulation answers `decapsHq Hq cst`
up to its stop index and measures its final projector. -/
def qIndcpaAuxRun (D : QIndAuxAdv ι (m₁ + m₂) n W q k c a PK C K M) (pk : PK) (cst : C)
    (Hq : C → K) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n) (T : C → Fin n) (z : Z) (x : ι) :
    ℝ≥0∞ :=
  prOut (truncAdv (toQAdv (D.prog pk cst (Hq cst) x) (decapsHq eC eKa Hq cst))
      (D.stop pk cst (Hq cst) x) (D.final pk cst (Hq cst) x)
      (D.final_conjTranspose pk cst (Hq cst) x) (D.final_mul_self pk cst (Hq cst) x))
    (auxOracle P hpk eG eJ eKR pk Hq G J T z)

/-- The probability that `D` outputs `1` in the IND-CPA game with challenge bit
`b`: the key pair under `keygen`, the coins of `D`, the encryption coins, the
seed and the tables uniform, and the challenge ciphertext the encryption of the
second message of `D` at `b = true` and of the first at `b = false`. -/
def qIndcpaAuxPr (D : QIndAuxAdv ι (m₁ + m₂) n W q k c a PK C K M) (b : Bool) : ℝ≥0∞ :=
  ∑ ks : PK × SK, P.keygen ks * ∑ x : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ *
    auxTabAvg fun r z G J Hq T =>
      qIndcpaAuxRun P hpk eG eJ eKR eC eKa D ks.1
        (P.enc ks.1 (if b then (D.msgs ks.1 x).2 else (D.msgs ks.1 x).1) r) Hq G J T z x

/-- The IND-CPA advantage with oracle access:
`|Pr[1 | b = true] - Pr[1 | b = false]|`. -/
def qIndcpaAux (D : QIndAuxAdv ι (m₁ + m₂) n W q k c a PK C K M) : ℝ≥0∞ :=
  absDiff (qIndcpaAuxPr P hpk eG eJ eKR eC eKa D true)
    (qIndcpaAuxPr P hpk eG eJ eKR eC eKa D false)

end Game

/-! ## The reduction -/

section Reduction

variable {m₁ m₂ n W q k c a : ℕ} {PK SK M C R K Hash ι : Type} [Nonempty M]
  (eG : (M × Hash) ≃ Fin m₁)

/-- The oracle points whose message is `m`. -/
def msgSet [DecidableEq M] (m : M) : Finset (Fin (m₁ + m₂)) :=
  Finset.univ.filter fun t => decodeG (m₂ := m₂) eG t = m

/-- The reduction: its coins are two messages and the coins of `B`; it runs `B`
on the public key and the challenge ciphertext, and outputs `1` when the
measured query register decodes to the second message. -/
def indRed [DecidableEq M] (B : QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K) :
    QIndAuxAdv (M × M × ι) (m₁ + m₂) n W q k c a PK C K M where
  msgs _ x := (x.1, x.2.1)
  prog pk cst h x := B.prog pk cst h x.2.2
  stop pk cst h x := B.stop pk cst h x.2.2
  final _ _ _ x := projS (m₁ + m₂) n (ancW c k W) (msgSet (m₂ := m₂) eG x.2.1)
  final_conjTranspose _ _ _ _ := projS_conjTranspose _ _ _ _
  final_mul_self _ _ _ _ := projS_mul_self _ _ _ _

/-- The weight of the key pairs, messages and encryption coins at which the
decryption of the encryption is not the message. -/
def corrErr [Fintype PK] [Fintype SK] [Fintype M] [Fintype R] [DecidableEq M]
    (P : Scheme PK SK M C R) : ℝ≥0∞ :=
  ∑ ks : PK × SK, P.keygen ks * ∑ m : M, (Fintype.card M : ℝ≥0∞)⁻¹ *
    ∑ r : R, (Fintype.card R : ℝ≥0∞)⁻¹ * if P.dec ks.2 (P.enc ks.1 m r) = some m then 0 else 1

end Reduction

/-! ## The bound -/

section Bound

/-- The inverse of a product of casts is the product of the inverses. -/
theorem inv_natCast_mul (x y : ℕ) :
    (((x * y : ℕ) : ℝ≥0∞))⁻¹ = (x : ℝ≥0∞)⁻¹ * (y : ℝ≥0∞)⁻¹ := by
  rw [Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

variable {m₁ m₂ n W q k c a : ℕ} {PK SK M C R K Hash Z ι : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  [Fintype ι] [Nonempty ι]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c]

/-- The prefix of `B` at coins `x` that measures whether its query register
decodes to `m`. -/
abbrev owPrefixAt (B : QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K) (pk : PK) (cst : C)
    (Hq : C → K) (x : ι) (m : M) : QAdv (m₁ + m₂) n (ancW c k W) (B.stop pk cst (Hq cst) x) :=
  queryPrefix (toQAdv (B.prog pk cst (Hq cst) x) (decapsHq eC eKa Hq cst))
    (msgSet (m₂ := m₂) eG m) (B.stop pk cst (Hq cst) x)

omit [Nonempty Z] [Nonempty R] [Nonempty ι] in
/-- `qOwcpaAux` written with `auxTabAvg`. -/
theorem qOwcpaAux_eq_auxTabAvg (B : QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K) :
    qOwcpaAux P hpk eG eJ eKR eC eKa B =
      ∑ ks : PK × SK, P.keygen ks * ∑ m : M, (Fintype.card M : ℝ≥0∞)⁻¹ *
        auxTabAvg fun r z G J Hq T =>
          qOwcpaAuxRun P hpk eG eJ eKR eC eKa B ks.1 ks.2 (P.enc ks.1 m r) Hq G J T z := rfl

omit [Fintype PK] [Fintype SK] [Fintype M] [Fintype Z] [Nonempty Z] [Fintype K] [Fintype R]
  [Nonempty R] [Fintype C] in
/-- The one-wayness win at the encryption of `m` is at most the probability
that the query register decodes to `m`, plus one when decryption of the
encryption is not `m`. -/
theorem qOwcpaAuxRun_le (B : QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K) (pk : PK) (sk : SK)
    (m : M) (r : R) (Hq : C → K) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n) (T : C → Fin n)
    (z : Z) :
    qOwcpaAuxRun P hpk eG eJ eKR eC eKa B pk sk (P.enc pk m r) Hq G J T z ≤
      (∑ x : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ *
        prOut (owPrefixAt eG eC eKa B pk (P.enc pk m r) Hq x m)
          (auxOracle P hpk eG eJ eKR pk Hq G J T z)) +
        if P.dec sk (P.enc pk m r) = some m then 0 else 1 := by
  by_cases hd : P.dec sk (P.enc pk m r) = some m
  · have hW : owWinSet (m₂ := m₂) P eG sk (P.enc pk m r) = msgSet (m₂ := m₂) eG m := by
      ext t
      simp [owWinSet, msgSet, hd, eq_comm]
    rw [if_pos hd, add_zero]
    unfold qOwcpaAuxRun
    rw [hW]
  · rw [if_neg hd]
    refine le_add_left ?_
    unfold qOwcpaAuxRun
    calc _ ≤ ∑ _x : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ * 1 := by
          gcongr
          exact prTrue_Q_le_one _ _
      _ = 1 := sum_inv_mul_const 1

omit [Nonempty Z] [Nonempty R] [Nonempty ι] in
/-- The probability that `indRed B` outputs `1` at `b = true` is the average
over the message of the probability that the query register of `B` decodes to
it. -/
theorem qIndcpaAuxPr_indRed_true (B : QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K) :
    qIndcpaAuxPr P hpk eG eJ eKR eC eKa (indRed eG B) true =
      ∑ ks : PK × SK, P.keygen ks * ∑ m : M, (Fintype.card M : ℝ≥0∞)⁻¹ *
        auxTabAvg fun r z G J Hq T => ∑ x : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ *
          prOut (owPrefixAt eG eC eKa B ks.1 (P.enc ks.1 m r) Hq x m)
            (auxOracle P hpk eG eJ eKR ks.1 Hq G J T z) := by
  unfold qIndcpaAuxPr
  refine Finset.sum_congr rfl fun ks _ => ?_
  congr 1
  rw [← sum_inv_mul_const (α := M) (∑ m : M, _), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun m₀ _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  simp only [auxTabAvg_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [auxTabAvg_mul_left, Fintype.card_prod, Fintype.card_prod, inv_natCast_mul,
    inv_natCast_mul]
  rw [mul_assoc, mul_assoc]
  rfl

/-- The probability that `indRed B` outputs `1` at `b = false` is at most
`|M|⁻¹`: the second message is independent of the view of `B`. -/
theorem qIndcpaAuxPr_indRed_false_le (B : QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K) :
    qIndcpaAuxPr P hpk eG eJ eKR eC eKa (indRed eG B) false ≤ (Fintype.card M : ℝ≥0∞)⁻¹ := by
  have hkey : ∑ ks, P.keygen ks = 1 := by
    have := P.keygen.tsum_coe; rwa [tsum_fintype] at this
  unfold qIndcpaAuxPr
  calc _ ≤ ∑ ks : PK × SK, P.keygen ks * (Fintype.card M : ℝ≥0∞)⁻¹ := by
        gcongr with ks
        rw [Fintype.sum_prod_type]
        calc _ = ∑ m₀ : M, ∑ x : ι, (Fintype.card M : ℝ≥0∞)⁻¹ * ((Fintype.card ι : ℝ≥0∞)⁻¹ *
              ((Fintype.card M : ℝ≥0∞)⁻¹ * ∑ m₁ : M, auxTabAvg fun r z G J Hq T =>
                prOut (owPrefixAt eG eC eKa B ks.1 (P.enc ks.1 m₀ r) Hq x m₁)
                  (auxOracle P hpk eG eJ eKR ks.1 Hq G J T z))) := by
              refine Finset.sum_congr rfl fun m₀ _ => ?_
              rw [Fintype.sum_prod_type, Finset.sum_comm]
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun m₁ _ => ?_
              rw [Fintype.card_prod, Fintype.card_prod, inv_natCast_mul, inv_natCast_mul]
              simp only [mul_assoc]
              ring_nf
              rfl
          _ ≤ ∑ _m₀ : M, ∑ _x : ι, (Fintype.card M : ℝ≥0∞)⁻¹ *
                ((Fintype.card ι : ℝ≥0∞)⁻¹ * ((Fintype.card M : ℝ≥0∞)⁻¹ * 1)) := by
              gcongr with m₀ _ x _
              rw [← auxTabAvg_sum]
              calc _ ≤ auxTabAvg (m₁ := m₁) (m₂ := m₂) (n := n) (C := C) (K := K) (R := R)
                    (Z := Z) (fun _ _ _ _ _ _ => 1) :=
                    auxTabAvg_mono fun r z G J Hq T =>
                      sum_prOut_queryPrefix_fiber_le_one _ _ _ (decodeG (m₂ := m₂) eG)
                _ = 1 := auxTabAvg_const 1
          _ = (Fintype.card M : ℝ≥0∞)⁻¹ := by
              simp only [mul_one, mul_left_comm (Fintype.card M : ℝ≥0∞)⁻¹
                (Fintype.card ι : ℝ≥0∞)⁻¹, sum_inv_mul_const]
    _ = (Fintype.card M : ℝ≥0∞)⁻¹ := by rw [← Finset.sum_mul, hkey, one_mul]

/-- One-wayness from IND-CPA with oracle access: the winning probability of `B`
in `qOwcpaAux` is at most the IND-CPA advantage of `indRed B`, plus `|M|⁻¹`,
plus the decryption error `corrErr P`.

References: Hofheinz, Hövelmanns, Kiltz, "A modular analysis of the
Fujisaki-Okamoto transformation", TCC 2017, ePrint 2017/604 (OW-CPA from
IND-CPA with the `1/|M|` term). -/
theorem qOwcpaAux_le_qIndcpaAux (B : QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K) :
    qOwcpaAux P hpk eG eJ eKR eC eKa B ≤
      qIndcpaAux P hpk eG eJ eKR eC eKa (indRed eG B) + (Fintype.card M : ℝ≥0∞)⁻¹ +
        corrErr P := by
  have h1 : qOwcpaAux P hpk eG eJ eKR eC eKa B ≤
      qIndcpaAuxPr P hpk eG eJ eKR eC eKa (indRed eG B) true + corrErr P := by
    rw [qOwcpaAux_eq_auxTabAvg, qIndcpaAuxPr_indRed_true]
    calc _ ≤ ∑ ks : PK × SK, P.keygen ks * ∑ m : M, (Fintype.card M : ℝ≥0∞)⁻¹ *
          auxTabAvg (fun r z G J Hq T => (∑ x : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ *
            prOut (owPrefixAt eG eC eKa B ks.1 (P.enc ks.1 m r) Hq x m)
              (auxOracle P hpk eG eJ eKR ks.1 Hq G J T z)) +
            if P.dec ks.2 (P.enc ks.1 m r) = some m then 0 else 1) := by
          gcongr with ks _ m _
          exact auxTabAvg_mono fun r z G J Hq T =>
            qOwcpaAuxRun_le P hpk eG eJ eKR eC eKa B ks.1 ks.2 m r Hq G J T z
      _ = _ := by
          unfold corrErr
          simp only [auxTabAvg_add, auxTabAvg_of_coins, mul_add, Finset.sum_add_distrib]
  have h2 : qIndcpaAuxPr P hpk eG eJ eKR eC eKa (indRed eG B) true ≤
      qIndcpaAux P hpk eG eJ eKR eC eKa (indRed eG B) + (Fintype.card M : ℝ≥0∞)⁻¹ :=
    le_tsub_add.trans (add_le_add (le_max_left _ _)
      (qIndcpaAuxPr_indRed_false_le P hpk eG eJ eKR eC eKa B))
  exact h1.trans (add_le_add h2 le_rfl)

end Bound

end CatCrypt.Quantum.QROM
