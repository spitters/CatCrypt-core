/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.HopCoinChallenge
public import CatCryptCore.Quantum.QROM.SparseSearch

/-!
# A quantum one-wayness game with oracle access, and the query-keeping reduction

The coin hop of `Quantum/QROM/HopCoinChallenge.lean` bounds its `Find` term by
the guessing probabilities of the reprogrammed game. This module states those
probabilities as the winning probability of a quantum one-wayness game in which
the challenger owns the random-oracle tables and the adversary queries them.

## Main definitions

* `queryPrefix A S j` — the adversary that runs `A` up to and including `U_j`
  with its first `j` oracle calls kept as oracle calls, then measures `projS S`
* `owWinSet P eG sk cst` — the oracle points whose message decrypts from `cst`
  under `sk`
* `auxOracle` — the merged oracle of the reprogrammed game as a function of the
  public key and the challenger's tables `Hq`, `G`, `J`, `T` and seed `z`
* `QOwAuxAdv ι` — an adversary of the game: from the public key, the challenge
  ciphertext, the value of `Hq` at it and its own coins in `ι`, a multi-round
  adversary and a query index at which it stops
* `qOwcpaAux P … B` — the winning probability: the challenger draws the key pair,
  the message, the coins and the tables, runs the adversary against `auxOracle`
  with decapsulation answers `decapsHq Hq c*` up to its stop index, measures the
  query register and accepts when the message of the outcome decrypts from `c*`
* `owRedQuery A b` — the reduction: coins a fake key and a query index, the KEM
  adversary run on the challenge key or the fake key, stopped at the index

## Main results

* `prOut_queryPrefix` — `prOut (queryPrefix A S j) H = guessProb A H S j`
* `guessProb_singleton_le` — the guessing probability at a point is at most the
  one at a set, plus one when the point is outside the set
* `prFindCoin_le_qOwcpaAux` —
  `prFindCoin A b ≤ 4 q' (qOwcpaAux (owRedQuery A b) + δ*)`

## The reduction and the game

The code of `owRedQuery A b` is the unitaries of `A`, its oracle calls to the
challenger's merged oracle, its classical rounds, and one measurement of the
query register. It draws a fake key and a query index and contains no
whole-table sample and no computation of a measurement distribution. Its cost
is that of `A` up to the stop index. The rounds run in the deferred form of
`toQAdv`: the outcome is recorded on an ancilla and the answer unitary is
controlled on the record, so each round evaluates `decapsHq Hq c*` at one
ciphertext, a classical query to `Hq`. The challenge key at bit `true` is `Hq`
at `c*`, which the game hands to the adversary as the answer of one classical
query. The merged oracle `auxOracle` evaluates `G`, `Hq`, `J`, `T` and one
encryption at the queried point. The query-register measurement of the
truncated deferred run is the game's definition of the adversary's output;
`qOwcpaAux_eq_measured` (`Quantum/QROM/QOwcpaAuxMeasured.lean`) identifies it
with the run whose decapsulation rounds are measured.

`δ*` is the weight of the inputs whose challenge message is outside `kemGood`.

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], Theorem 2
* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.2
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The prefix that keeps its oracle calls -/

section Prefix

variable {m n w q : ℕ}

/-- The adversary that runs `A` up to and including `U_j`, with the first `j`
oracle calls kept as oracle calls, and measures `projS S`. -/
def queryPrefix (A : QAdv m n w q) (S : Finset (Fin m)) (j : Fin q) : QAdv m n w j where
  U i := A.U (Fin.castLE (Nat.succ_le_succ j.isLt.le) i)
  init := A.init
  final := projS m n w S
  final_conjTranspose := projS_conjTranspose m n w S
  final_mul_self := projS_mul_self m n w S

variable [NeZero n]

/-- Absorbing the oracle into `queryPrefix` gives `prefixAdv`. -/
theorem absorbOracle_queryPrefix (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    (j : Fin q) : absorbOracle (queryPrefix A S j) H = prefixAdv A H S j := rfl

/-- The prefix with its oracle calls wins against `H` with the guessing
probability of `A` against `H`. -/
theorem prOut_queryPrefix (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    (j : Fin q) : prOut (queryPrefix A S j) H = guessProb A H S j := by
  unfold guessProb
  rw [← absorbOracle_queryPrefix, prOut_absorbOracle]

/-- The guessing probability at a point is at most the one at a set `W`, plus
one when the point is outside `W`. -/
theorem guessProb_singleton_le (A : QAdv m n w q) (H : Fin m → Fin n) (t : Fin m)
    (W : Finset (Fin m)) (j : Fin q) {ψ : Fin (m * n * w) → ℂ}
    (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    guessProb A H {t} j ≤ guessProb A H W j + if t ∈ W then 0 else 1 := by
  by_cases ht : t ∈ W
  · rw [ite_eq_left ht, add_zero, guessProb_eq_sum A H W j hpure]
    exact Finset.single_le_sum (f := fun x => guessProb A H {x} j) (fun _ _ => zero_le) ht
  · rw [ite_eq_right ht]
    exact ((Finset.single_le_sum (f := fun x => guessProb A H {x} j) (fun _ _ => zero_le)
      (Finset.mem_univ t)).trans (sum_guessProb_singleton_le_one A H j hpure)).trans le_add_self

end Prefix

/-! ## The game -/

/-- An adversary of `qOwcpaAux` with coins in `ι`: from the public key, the
challenge ciphertext, a key and its coins, a multi-round adversary and the
index of the query before which it stops. -/
structure QOwAuxAdv (ι : Type) (m n W q k c a : ℕ) (PK C K : Type) where
  /-- The multi-round adversary it runs. -/
  prog : PK → C → K → ι → QAdvMR m n W q k c a
  /-- The query index at which the run stops. -/
  stop : PK → C → K → ι → Fin (flatQ q k q)

section Game

variable {m₁ m₂ n W q k c a : ℕ} {PK SK M C R K Hash Z ι : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [DecidableEq Z] [Fintype K] [Nonempty K]
  [Fintype R] [Fintype C] [DecidableEq C] [DecidableEq Hash] [Fintype ι]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

/-- The oracle points whose message decrypts from `cst` under `sk`. -/
def owWinSet (sk : SK) (cst : C) : Finset (Fin (m₁ + m₂)) :=
  Finset.univ.filter fun t => P.dec sk cst = some (decodeG (m₂ := m₂) eG t)

/-- The merged oracle of the reprogrammed coin game at the public key `pk`, the
tables `Hq`, `G`, `J`, `T` and the seed `z`: the `G`-part carries on the
public-key slice the key `Hq` at the ciphertext of each point, and the `J`-part
has its `z`-prefix replaced by `T`. -/
def auxOracle (pk : PK) (Hq : C → K) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n)
    (T : C → Fin n) (z : Z) : Fin (m₁ + m₂) → Fin n :=
  mergeOracle (keyHop (kemSlice hpk eG pk) (kemEncAt P eG pk) eKR.symm Hq G)
    (prefixUpdate eJ z J T)

variable [NeZero n] [NeZero c]

/-- The winning probability of `B` at a key pair, a challenge ciphertext and
the challenger's tables: `B` draws its coins, receives `pk`, `cst` and `Hq cst`,
runs against `auxOracle` with decapsulation answers `decapsHq Hq cst` up to its
stop index, and wins when the measured query register lies in `owWinSet`. -/
def qOwcpaAuxRun (B : QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K) (pk : PK) (sk : SK) (cst : C)
    (Hq : C → K) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n) (T : C → Fin n) (z : Z) : ℝ≥0∞ :=
  ∑ x : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ *
    prOut (queryPrefix (toQAdv (B.prog pk cst (Hq cst) x) (decapsHq eC eKa Hq cst))
        (owWinSet P eG sk cst) (B.stop pk cst (Hq cst) x))
      (auxOracle P hpk eG eJ eKR pk Hq G J T z)

/-- The quantum one-wayness game with oracle access: the key pair under
`keygen`, the message, the coins, the seed and the tables `G`, `J`, `Hq`, `T`
uniform, the challenge ciphertext the encryption of the message, and the
winning probability `qOwcpaAuxRun`. -/
def qOwcpaAux (B : QOwAuxAdv ι (m₁ + m₂) n W q k c a PK C K) : ℝ≥0∞ :=
  ∑ ks : PK × SK, P.keygen ks * ∑ m : M, (Fintype.card M : ℝ≥0∞)⁻¹ *
    ∑ r : R, (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ z : Z, (Fintype.card Z : ℝ≥0∞)⁻¹ *
      ∑ G : Fin m₁ → Fin n, (Fintype.card (Fin m₁ → Fin n) : ℝ≥0∞)⁻¹ *
        ∑ J : Fin m₂ → Fin n, (Fintype.card (Fin m₂ → Fin n) : ℝ≥0∞)⁻¹ *
          ∑ Hq : C → K, (Fintype.card (C → K) : ℝ≥0∞)⁻¹ *
            ∑ T : C → Fin n, (Fintype.card (C → Fin n) : ℝ≥0∞)⁻¹ *
              qOwcpaAuxRun P hpk eG eJ eKR eC eKa B ks.1 ks.2 (P.enc ks.1 m r) Hq G J T z

end Game

/-! ## The reduction -/

section Reduction

variable {m₁ m₂ n w q k c a : ℕ} {PK C K : Type}

/-- The reduction: its coins are a fake key `kf` and a query index `j`; it runs
the KEM adversary on the challenge key it receives at `b = true` and on `kf` at
`b = false`, and stops before query `j`. -/
def owRedQuery (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    QOwAuxAdv (K × Fin (flatQ q k q)) (m₁ + m₂) n (2 * w) q k c a PK C K where
  prog pk cst h x := A.run pk cst (if b then h else x.1)
  stop _ _ _ x := x.2

end Reduction

/-! ## The bound -/

section Sums

/-- Five nested finite sums with the first moved to the back. -/
theorem sum_comm_five {α β γ δ ε : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] (f : α → β → γ → δ → ε → ℝ≥0∞) :
    ∑ x₁, ∑ x₂, ∑ x₃, ∑ x₄, ∑ x₅, f x₁ x₂ x₃ x₄ x₅ =
      ∑ x₂, ∑ x₃, ∑ x₄, ∑ x₅, ∑ x₁, f x₁ x₂ x₃ x₄ x₅ := by
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun x₂ _ => ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun x₃ _ => ?_)
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun x₄ _ => ?_)
  exact Finset.sum_comm

end Sums

section Final

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c] [NeZero (flatQ q k q)]

/-- The summed winning probabilities of the prefixes of the KEM adversary at a
key pair, a challenge ciphertext, the challenger's tables and a fake key. -/
def auxWin (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) (pk : PK) (sk : SK) (cst : C)
    (Hq : C → K) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n) (T : C → Fin n) (z : Z) (kf : K) :
    ℝ≥0∞ :=
  ∑ j : Fin (flatQ q k q),
    prOut (queryPrefix (toQAdv (A.run pk cst (if b then Hq cst else kf)) (decapsHq eC eKa Hq cst))
      (owWinSet P eG sk cst) j) (auxOracle P hpk eG eJ eKR pk Hq G J T z)

omit [Fintype R] [NeZero (flatQ q k q)] in
/-- The summed guessing probabilities of the coin hop at the challenge point are
at most `auxWin` at the view of the hop, plus `q'` when the challenge message is
outside `kemGood`. -/
theorem sum_guessProb_hopCoinGame_le (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (p : KEMInput PK SK Z M K m₁ m₂ n × Fin n × (C → K) × (C → Fin n)) :
    ∑ j : Fin (flatQ q k q), guessProb ((hopCoinGame P hpk eG eJ eKR eC eKa A b).adv p)
        ((hopCoinGame P hpk eG eJ eKR eC eKa A b).oracle' p)
        ((hopCoinGame P hpk eG eJ eKR eC eKa A b).S p) j ≤
      auxWin P hpk eG eJ eKR eC eKa A b p.1.1.1 p.1.1.2 (kemChal P hpk eG eKR p.1) p.2.2.1
          (Function.update p.1.2.2.2.2.1 (kemPt hpk eG p.1) p.2.1) p.1.2.2.2.2.2 p.2.2.2 p.1.2.1
          p.1.2.2.2.1 +
        (flatQ q k q : ℝ≥0∞) * (if p.1.2.2.1 ∈ kemGood P hpk eG eKR p.1 then 0 else 1) := by
  set Gm := hopCoinGame P hpk eG eJ eKR eC eKa A b with hGm
  obtain ⟨ψ, hψ⟩ := Gm.pure p
  have hS : Gm.S p = {kemPtMerged hpk eG p.1} := mergeSet_kemPt_eq_singleton hpk eG p.1
  set W := owWinSet (m₂ := m₂) P eG p.1.1.2 (kemChal P hpk eG eKR p.1) with hW
  have hind : (if kemPtMerged hpk eG p.1 ∈ W then (0 : ℝ≥0∞) else 1) ≤
      if p.1.2.2.1 ∈ kemGood P hpk eG eKR p.1 then 0 else 1 := by
    by_cases hg : p.1.2.2.1 ∈ kemGood P hpk eG eKR p.1
    · have hmem : kemPtMerged hpk eG p.1 ∈ W := by
        rw [hW, owWinSet, Finset.mem_filter, decodeG_kemPtMerged]
        exact ⟨Finset.mem_univ _, (mem_good_iff _ _ _ _).1 hg⟩
      rw [ite_eq_left hmem, ite_eq_left hg]
    · rw [ite_eq_right hg]
      split_ifs <;> simp
  calc ∑ j, guessProb (Gm.adv p) (Gm.oracle' p) (Gm.S p) j
      ≤ ∑ j : Fin (flatQ q k q), (guessProb (Gm.adv p) (Gm.oracle' p) W j +
          if p.1.2.2.1 ∈ kemGood P hpk eG eKR p.1 then 0 else 1) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [hS]
        exact (guessProb_singleton_le _ _ _ W j hψ).trans (add_le_add le_rfl hind)
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← prOut_queryPrefix]
        rfl

omit [Fintype R] [NeZero (flatQ q k q)] in
/-- The exchange `ptSwap` moves the coin of the challenge ciphertext to the
fresh value and the reprogrammed table to the input's own `G`-table. -/
theorem sum_auxWin_ptSwap (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    ∑ p, (hopCoinGame P hpk eG eJ eKR eC eKa A b).sample p *
        auxWin P hpk eG eJ eKR eC eKa A b p.1.1.1 p.1.1.2 (kemChal P hpk eG eKR p.1) p.2.2.1
          (Function.update p.1.2.2.2.2.1 (kemPt hpk eG p.1) p.2.1) p.1.2.2.2.2.2 p.2.2.2 p.1.2.1
          p.1.2.2.2.1 =
      ∑ p, (hopCoinGame P hpk eG eJ eKR eC eKa A b).sample p *
        auxWin P hpk eG eJ eKR eC eKa A b p.1.1.1 p.1.1.2
          (P.enc p.1.1.1 p.1.2.2.1 (eKR.symm p.2.1).2) p.2.2.1 p.1.2.2.2.2.1 p.1.2.2.2.2.2
          p.2.2.2 p.1.2.1 p.1.2.2.2.1 :=
  Fintype.sum_equiv ((ptSwap_involutive hpk eG).toPerm _) _ _ fun _ => rfl

omit [Fintype PK] [Fintype SK] [Fintype M] [Fintype Z] [Nonempty Z] [Fintype R] [Nonempty R]
  [Fintype C] [NeZero (flatQ q k q)] in
/-- The winning probability of `owRedQuery` is the uniform average of `auxWin`
over the fake key, divided by `q'`. -/
theorem qOwcpaAuxRun_owRedQuery (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) (pk : PK)
    (sk : SK) (cst : C) (Hq : C → K) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n) (T : C → Fin n)
    (z : Z) :
    qOwcpaAuxRun P hpk eG eJ eKR eC eKa (owRedQuery A b) pk sk cst Hq G J T z =
      ∑ kf : K, (flatQ q k q : ℝ≥0∞)⁻¹ * ((Fintype.card K : ℝ≥0∞)⁻¹ *
        auxWin P hpk eG eJ eKR eC eKa A b pk sk cst Hq G J T z kf) := by
  unfold qOwcpaAuxRun auxWin
  rw [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  refine Finset.sum_congr rfl fun kf _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [owRedQuery]
  ring

/-- The swapped sum of `auxWin` is `q'` times the winning probability of
`owRedQuery` in `qOwcpaAux`. -/
theorem sum_auxWin_eq_qOwcpaAux (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    ∑ p, (hopCoinGame P hpk eG eJ eKR eC eKa A b).sample p *
        auxWin P hpk eG eJ eKR eC eKa A b p.1.1.1 p.1.1.2
          (P.enc p.1.1.1 p.1.2.2.1 (eKR.symm p.2.1).2) p.2.2.1 p.1.2.2.2.2.1 p.1.2.2.2.2.2
          p.2.2.2 p.1.2.1 p.1.2.2.2.1 =
      (flatQ q k q : ℝ≥0∞) * qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery A b) := by
  refine (natCast_mul_inv_mul (q := flatQ q k q) _).symm.trans ?_
  congr 1
  unfold qOwcpaAux
  simp only [qOwcpaAuxRun_owRedQuery, sum_coin_avg eKR]
  simp only [hopCoinGame, kemSample, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun pk _ => Finset.sum_congr rfl fun sk _ => ?_
  rw [sum_reorder8]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  rw [sum_comm_five]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  simp only [tabWeight, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  ring

/-- The `Find` probability of the coin hop is at most `4 q'` times the winning
probability of `owRedQuery` in `qOwcpaAux` plus the weight of the inputs whose
challenge message is outside `kemGood`.

References: Ambainis, Hamburg, Unruh, "Quantum security proofs using
semi-classical oracles", CRYPTO 2019, ePrint 2018/904, Theorem 2 (the search
bound turning `Pr[Find]` into a guessing probability); Hofheinz, Hövelmanns,
Kiltz, "A modular analysis of the Fujisaki-Okamoto transformation", TCC 2017,
ePrint 2017/604, and Targhi, Unruh, "Post-quantum security of the
Fujisaki-Okamoto and OAEP transforms", TCC 2016, ePrint 2015/1210 (OW-CPA as
the target of the derandomisation step). -/
theorem prFindCoin_le_qOwcpaAux (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prFindCoin P hpk eG eJ eKR eC eKa A b ≤
      4 * (flatQ q k q : ℝ≥0∞) *
        (qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery A b) +
          ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
            (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)) := by
  set G := hopCoinGame P hpk eG eJ eKR eC eKa A b with hG
  calc prFindCoin P hpk eG eJ eKR eC eKa A b
      ≤ 4 * ∑ j : Fin (flatQ q k q), ∑ p, G.sample p *
          guessProb (G.adv p) (G.oracle' p) (G.S p) j :=
        prFindAvg_le_four_sum_guess G
    _ = 4 * ∑ p, G.sample p * ∑ j : Fin (flatQ q k q),
          guessProb (G.adv p) (G.oracle' p) (G.S p) j := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ ≤ 4 * ∑ p, G.sample p *
          (auxWin P hpk eG eJ eKR eC eKa A b p.1.1.1 p.1.1.2 (kemChal P hpk eG eKR p.1) p.2.2.1
            (Function.update p.1.2.2.2.2.1 (kemPt hpk eG p.1) p.2.1) p.1.2.2.2.2.2 p.2.2.2
            p.1.2.1 p.1.2.2.2.1 +
          (flatQ q k q : ℝ≥0∞) * (fun i : KEMInput PK SK Z M K m₁ m₂ n =>
            if i.2.2.1 ∈ kemGood P hpk eG eKR i then (0 : ℝ≥0∞) else 1) p.1) := by
        gcongr with p
        exact sum_guessProb_hopCoinGame_le P hpk eG eJ eKR eC eKa A b p
    _ = 4 * ((flatQ q k q : ℝ≥0∞) * qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery A b) +
          (flatQ q k q : ℝ≥0∞) * ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
            (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)) := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [hG, sum_auxWin_ptSwap, sum_auxWin_eq_qOwcpaAux,
          ← sum_hopCoinGame_sample_fst P hpk eG eJ eKR eC eKa A b]
        congr 1
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
    _ = _ := by ring

end Final

end CatCrypt.Quantum.QROM
