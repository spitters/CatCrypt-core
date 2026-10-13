/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.HopDecaps
public import CatCryptCore.Quantum.QROM.FindToGuess

/-!
# The challenge-key hop: reprogramming `G` at the challenge point

In the game `prWinKEMSim` of `Quantum/QROM/HopDecaps.lean` the challenge key at
`b = true` is the key part of the `G`-table at the challenge point
`eG (m*, hpk pk)`, and at `b = false` an independent uniform key. This module
reprograms the adversary's `G`-table at that one point by a fresh uniform value
`u : Fin n`. The reprogrammed oracle agrees with the original outside the
singleton, so the averaged one-way-to-hiding bound of
`Quantum/QROM/QAdvGame.lean` applies.

In the reprogrammed game the key part of the table at the challenge point
occurs only as the challenge key: the adversary's oracle carries `u` there, and
the simulated decapsulation reads that key part only at the challenge
ciphertext, which `decapsSim` answers by a fixed key. Exchanging the key part
of the table entry at the challenge point with the independent key of the input
is therefore an involution of the input under which the whole game summand is
invariant except for the challenge key, and the two bits give the same
probability.

## Main definitions

* `simKeyAt_congr` — the ciphertext lookup at two tables with equal coins
* `kemPt` — the challenge point `eG (m*, hpk pk)` on the first summand
* `kemOracleK i u` — the merged oracle with the `G`-table updated at `kemPt` by `u`
* `keySwap`, `keySwapEquiv` — the involution of the input exchanging the key
  part of the table entry at `kemPt` with the independent key
* `prWinKEMK` — the winning probability with the reprogrammed oracle, averaged
  over the fresh value
* `hopKGame` — the hop as a `QGame` over `KEMInput × Fin n`
* `prFindAvgK` — the averaged `Find` probability of `hopKGame`
* `qINDCCAAdvantageSim` — the advantage in the game with simulated decapsulation

## Main results

* `kemOracleK_agree` — the two oracles agree outside `mergeSet {kemPt} ∅`
* `decapsSim_keySwap` — the simulated decapsulation is invariant under `keySwap`
* `prWinKEMK_indep` — the two bits give the same probability in the
  reprogrammed game
* `prWinKEMSim_eq_prWin`, `prWinKEMK_eq_prWin'` — the two probabilities are
  those of `hopKGame`
* `hopK_o2h` — `|prWinKEMSim − prWinKEMK| ≤ 4 √(q' · prFindAvgK A b)`
* `hopK` — `qINDCCAAdvantageSim A ≤ 8 √(q' · (prFindAvgK A true ⊔ prFindAvgK A false))`
* `prFindAvgK_le` — the averaged `Find` probability is at most four times the
  averaged guessing probability at the challenge point, summed over the queries

## Scope

The bound is over `prWinKEMSim`, the game of `Quantum/QROM/HopDecaps.lean`
whose decapsulation reads the `G`-table instead of the secret key, not over
`prWinKEM`; composing the hops `hopJ`, `hopD` and `hopK` into the U-step is a
separate module. `prWinKEMK_indep` is unconditional, and the fact that carries
it is the reprogramming: the summand at a fixed fresh value depends on the key
part of the `G`-table at the challenge point only through the challenge key,
because `kemOracleK` overwrites that entry and `decapsSim` reads it only at the
challenge ciphertext, where it answers with a fixed key. `hopK_o2h` rests on the
agreement of the two oracles outside the singleton, and `hopK` on
`prWinKEMK_indep` through the triangle inequality. `prFindAvgK_le` leaves the
identification of the guessing probability with an OW-CPA reduction to a
further module.

## References

* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.2
* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], §3
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The ciphertext lookup at two tables with equal coins -/

section Congr

variable {M C Key Coin : Type}

open scoped Classical in
/-- Two key-and-coin tables with the same coins have the same ciphertext lookup
at a ciphertext whose messages carry the same key in both. -/
theorem simKeyAt_congr {enc : M → Coin → C} {T T' : M → Key × Coin}
    (hcoin : ∀ m, (T m).2 = (T' m).2) {c : C}
    (hkey : ∀ m, encOf enc T m = c → (T m).1 = (T' m).1) :
    simKeyAt enc T c = simKeyAt enc T' c := by
  have he : encOf enc T = encOf enc T' := by
    funext m; simp only [encOf, encAt, coinsOf, hcoin m]
  simp only [simKeyAt, he]
  split_ifs with h
  · rw [hkey h.choose (by rw [he]; exact h.choose_spec)]
  · rfl

end Congr

/-! ## The reprogrammed oracle -/

section Reprogram

variable {m₁ m₂ n : ℕ} {PK SK M C R K Hash Z : Type} (hpk : PK → Hash)
  (eG : (M × Hash) ≃ Fin m₁) (eKR : (K × R) ≃ Fin n)

/-- The challenge point: the index of `(m*, hpk pk)` on the first summand. -/
def kemPt (i : KEMInput PK SK Z M K m₁ m₂ n) : Fin m₁ := eG (i.2.2.1, hpk i.1.1)

/-- The merged oracle with the `G`-table updated at the challenge point by `u`. -/
def kemOracleK (i : KEMInput PK SK Z M K m₁ m₂ n) (u : Fin n) : Fin (m₁ + m₂) → Fin n :=
  mergeOracle (Function.update i.2.2.2.2.1 (kemPt hpk eG i) u) i.2.2.2.2.2

/-- `kemOracle i` and `kemOracleK i u` agree outside the challenge point. -/
theorem kemOracleK_agree (i : KEMInput PK SK Z M K m₁ m₂ n) (u : Fin n) :
    ∀ x, x ∉ mergeSet {kemPt hpk eG i} (∅ : Finset (Fin m₂)) →
      kemOracle i x = kemOracleK hpk eG i u x :=
  mergeOracle_agree
    (fun x hx => (Function.update_of_ne (by simpa using hx) _ _).symm) (fun _ _ => rfl)

end Reprogram

/-! ## The involution exchanging the challenge key with the independent key -/

section Swap

variable {m₁ m₂ n : ℕ} {PK SK M C R K Hash Z : Type} (hpk : PK → Hash)
  (eG : (M × Hash) ≃ Fin m₁) (eKR : (K × R) ≃ Fin n)

/-- The input with the key part of the `G`-table entry at the challenge point
and the independent key exchanged. -/
def keySwap (i : KEMInput PK SK Z M K m₁ m₂ n) : KEMInput PK SK Z M K m₁ m₂ n :=
  (i.1, i.2.1, i.2.2.1, (eKR.symm (i.2.2.2.2.1 (kemPt hpk eG i))).1,
    Function.update i.2.2.2.2.1 (kemPt hpk eG i)
      (eKR (i.2.2.2.1, (eKR.symm (i.2.2.2.2.1 (kemPt hpk eG i))).2)),
    i.2.2.2.2.2)

theorem kemPt_keySwap (i : KEMInput PK SK Z M K m₁ m₂ n) :
    kemPt hpk eG (keySwap hpk eG eKR i) = kemPt hpk eG i := rfl

theorem keySwap_fst (i : KEMInput PK SK Z M K m₁ m₂ n) :
    (keySwap hpk eG eKR i).1 = i.1 := rfl

theorem keySwap_seed (i : KEMInput PK SK Z M K m₁ m₂ n) :
    (keySwap hpk eG eKR i).2.1 = i.2.1 := rfl

theorem keySwap_involutive :
    Function.Involutive (keySwap (PK := PK) (SK := SK) (Z := Z) (m₂ := m₂) hpk eG eKR) := by
  intro i
  simp only [keySwap, kemPt, Function.update_self, Equiv.symm_apply_apply,
    Prod.mk.eta, Equiv.apply_symm_apply, Function.update_idem, Function.update_eq_self]

/-- The involution as an equivalence of the input type. -/
def keySwapEquiv :
    KEMInput PK SK Z M K m₁ m₂ n ≃ KEMInput PK SK Z M K m₁ m₂ n :=
  (keySwap_involutive hpk eG eKR).toPerm _

@[simp]
theorem keySwapEquiv_apply (i : KEMInput PK SK Z M K m₁ m₂ n) :
    keySwapEquiv hpk eG eKR i = keySwap hpk eG eKR i := rfl

theorem kemOracleK_keySwap (i : KEMInput PK SK Z M K m₁ m₂ n) (u : Fin n) :
    kemOracleK hpk eG (keySwap hpk eG eKR i) u = kemOracleK hpk eG i u := by
  simp only [kemOracleK, keySwap, kemPt, Function.update_idem]

theorem kemG_keySwap_coin (i : KEMInput PK SK Z M K m₁ m₂ n) (x : M × Hash) :
    (kemG eG eKR (keySwap hpk eG eKR i) x).2 = (kemG eG eKR i x).2 := by
  by_cases h : eG x = kemPt hpk eG i
  · simp [kemG, keySwap, h, Function.update_self, Equiv.symm_apply_apply]
  · simp [kemG, keySwap, Function.update_of_ne h]

theorem kemChal_keySwap (P : Scheme PK SK M C R) (i : KEMInput PK SK Z M K m₁ m₂ n) :
    kemChal P hpk eG eKR (keySwap hpk eG eKR i) = kemChal P hpk eG eKR i := by
  show P.enc i.1.1 i.2.2.1
      (kemG eG eKR (keySwap hpk eG eKR i) (i.2.2.1, hpk i.1.1)).2 = _
  rw [kemG_keySwap_coin hpk eG eKR i]
  rfl

theorem kemKey_keySwap_false (i : KEMInput PK SK Z M K m₁ m₂ n) :
    kemKey hpk eG eKR (keySwap hpk eG eKR i) false = kemKey hpk eG eKR i true := by
  simp [kemKey, keySwap, kemG, kemPt]

theorem kemJ_keySwap {eJ : (Z × C) ≃ Fin m₂} (i : KEMInput PK SK Z M K m₁ m₂ n) :
    kemJ eJ eKR (keySwap hpk eG eKR i) = kemJ eJ eKR i := rfl

theorem kemSample_keySwap [Fintype Z] [Fintype M] [Fintype K] (P : Scheme PK SK M C R)
    (i : KEMInput PK SK Z M K m₁ m₂ n) :
    kemSample P (keySwap hpk eG eKR i) = kemSample P i := rfl

end Swap

/-! ## The simulated decapsulation is invariant under the involution -/

section SwapDecaps

variable {m₁ m₂ n c a : ℕ} {PK SK M C R K Hash Z : Type} [Nonempty K] [DecidableEq C]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

omit [Nonempty K] [DecidableEq C] in
theorem kemTab_keySwap_coin (i : KEMInput PK SK Z M K m₁ m₂ n) (m : M) :
    (kemTab hpk eG eKR (keySwap hpk eG eKR i) m).2 = (kemTab hpk eG eKR i m).2 :=
  kemG_keySwap_coin hpk eG eKR i _

omit [Nonempty K] [DecidableEq C] in
/-- The ciphertext of the challenge message under the coins of the `G`-table is
the challenge ciphertext. -/
theorem encOf_kemTab_of_eq_pt (i : KEMInput PK SK Z M K m₁ m₂ n) (m : M)
    (h : eG (m, hpk i.1.1) = kemPt hpk eG i) :
    encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m = kemChal P hpk eG eKR i := by
  have hm : m = i.2.2.1 := congrArg Prod.fst (eG.injective h)
  subst hm
  rfl

omit [Nonempty K] [DecidableEq C] in
theorem kemTab_keySwap_key_of_ne (i : KEMInput PK SK Z M K m₁ m₂ n) (m : M)
    (h : eG (m, hpk i.1.1) ≠ kemPt hpk eG i) :
    (kemTab hpk eG eKR (keySwap hpk eG eKR i) m).1 = (kemTab hpk eG eKR i m).1 := by
  simp [kemTab, kemG, keySwap, Function.update_of_ne h]

omit [Nonempty K] [DecidableEq C] in
/-- Off the challenge ciphertext the lookup is the same at the two tables. -/
theorem simKeyAt_kemTab_keySwap (i : KEMInput PK SK Z M K m₁ m₂ n) (c' : C)
    (hc : c' ≠ kemChal P hpk eG eKR i) :
    simKeyAt (P.enc i.1.1) (kemTab hpk eG eKR (keySwap hpk eG eKR i)) c' =
      simKeyAt (P.enc i.1.1) (kemTab hpk eG eKR i) c' := by
  have hcoin := kemTab_keySwap_coin hpk eG eKR i
  refine simKeyAt_congr hcoin (fun m hm => ?_)
  refine kemTab_keySwap_key_of_ne hpk eG eKR i m fun hpt => hc ?_
  have henc : encOf (P.enc i.1.1) (kemTab hpk eG eKR (keySwap hpk eG eKR i)) m =
      encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m := by
    simp only [encOf, encAt, coinsOf, hcoin m]
  rw [← hm, henc, encOf_kemTab_of_eq_pt P hpk eG eKR i m hpt]

/-- The simulated classical function of the rounds is invariant under the
involution. -/
theorem decapsSim_keySwap (i : KEMInput PK SK Z M K m₁ m₂ n) :
    decapsSim P hpk eG eJ eKR eC eKa (keySwap hpk eG eKR i) =
      decapsSim P hpk eG eJ eKR eC eKa i := by
  funext x
  simp only [decapsSim, kemChal_keySwap, kemJ_keySwap, keySwap_fst, keySwap_seed]
  by_cases h : eC.symm x = kemChal P hpk eG eKR i
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, simKeyAt_kemTab_keySwap P hpk eG eKR i _ h]

end SwapDecaps

/-! ## The reprogrammed game -/

section Game

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [Fintype K] [Nonempty K]
  [Nonempty R] [Fintype C] [DecidableEq C] (P : Scheme PK SK M C R) (hpk : PK → Hash)
  (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c)
  (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c]

/-- The probability that `A` outputs `1` in the game with simulated
decapsulation and bit `b` when the `G`-table the adversary queries is
reprogrammed at the challenge point by a fresh uniform value. -/
def prWinKEMK (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) : ℝ≥0∞ :=
  ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ u : Fin n, kemSample P i * (n : ℝ≥0∞)⁻¹ *
    prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i) (kemKey hpk eG eKR i b))
      (kemOracleK hpk eG i u) (decapsSim P hpk eG eJ eKR eC eKa i)

omit [DecidableEq M] [Nonempty M] [Nonempty Z] [Nonempty R] [Fintype C] [NeZero c] in
/-- In the reprogrammed game the two challenge bits give the same probability. -/
theorem prWinKEMK_indep (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    prWinKEMK P hpk eG eJ eKR eC eKa A true = prWinKEMK P hpk eG eJ eKR eC eKa A false := by
  unfold prWinKEMK
  refine Fintype.sum_equiv (keySwapEquiv hpk eG eKR) _ _ fun i => ?_
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [keySwapEquiv_apply, kemChal_keySwap, kemKey_keySwap_false, kemOracleK_keySwap,
    decapsSim_keySwap, kemSample_keySwap, keySwap_fst]

/-- The hop as a `QGame` over the input and the fresh value: the adversary is
the single-run embedding of `A` at the simulated decapsulation function, the
oracle is `kemOracle i`, the reprogrammed oracle is `kemOracleK i u`, and the
punctured set is the challenge point. -/
def hopKGame (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    QGame (m₁ + m₂) n (ancW c k (2 * w)) (flatQ q k q)
      (KEMInput PK SK Z M K m₁ m₂ n × Fin n) where
  sample p := kemSample P p.1 * (n : ℝ≥0∞)⁻¹
  sample_sum := by
    have hn : (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top n)
    rw [Fintype.sum_prod_type]
    have h : ∀ i : KEMInput PK SK Z M K m₁ m₂ n,
        (∑ _u : Fin n, kemSample P i * (n : ℝ≥0∞)⁻¹) = kemSample P i := by
      intro i
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        show (n : ℝ≥0∞) * (kemSample P i * (n : ℝ≥0∞)⁻¹) =
          ((n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) * kemSample P i from by ring, hn, one_mul]
    simp only [h]
    exact kemSample_sum (Z := Z) (K := K) P eKR
  adv p := toQAdv (A.run p.1.1.1 (kemChal P hpk eG eKR p.1) (kemKey hpk eG eKR p.1 b))
    (decapsSim P hpk eG eJ eKR eC eKa p.1)
  oracle p := kemOracle p.1
  oracle' p := kemOracleK hpk eG p.1 p.2
  S p := mergeSet {kemPt hpk eG p.1} ∅
  agree p := kemOracleK_agree hpk eG p.1 p.2
  pure p := by
    obtain ⟨ψ, hψ⟩ := A.pure p.1.1.1 (kemChal P hpk eG eKR p.1) (kemKey hpk eG eKR p.1 b)
    exact pure_toQAdv _ _ hψ

omit [DecidableEq M] [Fintype C] in
/-- The winning probability with simulated decapsulation is `prWin` of the hop
game. -/
theorem prWinKEMSim_eq_prWin (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinKEMSim P hpk eG eJ eKR eC eKa A b = prWin (hopKGame P hpk eG eJ eKR eC eKa A b) := by
  have hn : (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top n)
  unfold prWinKEMSim prWin
  conv_rhs => rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ X : ℝ≥0∞, (n : ℝ≥0∞) * (kemSample P i * (n : ℝ≥0∞)⁻¹ * X) = kemSample P i * X := by
    intro X
    rw [show (n : ℝ≥0∞) * (kemSample P i * (n : ℝ≥0∞)⁻¹ * X) =
      ((n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) * (kemSample P i * X) from by ring, hn, one_mul]
  simp only [hopKGame, ← prOutMR_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, h]

omit [DecidableEq M] [Fintype C] in
/-- The reprogrammed winning probability is `prWin'` of the hop game. -/
theorem prWinKEMK_eq_prWin' (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinKEMK P hpk eG eJ eKR eC eKa A b = prWin' (hopKGame P hpk eG eJ eKR eC eKa A b) := by
  simp only [prWinKEMK, prWin', hopKGame, Fintype.sum_prod_type, prOutMR_eq]

/-- The averaged `Find` probability of the hop. -/
def prFindAvgK (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) : ℝ≥0∞ :=
  prFindAvg (hopKGame P hpk eG eJ eKR eC eKa A b)

omit [DecidableEq M] [Fintype C] in
/-- The one-way-to-hiding step of the hop:
`|prWinKEMSim − prWinKEMK| ≤ 4 √(q' · prFindAvgK A b)` with `q' = flatQ q k q`. -/
theorem hopK_o2h (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    absDiff (prWinKEMSim P hpk eG eJ eKR eC eKa A b) (prWinKEMK P hpk eG eJ eKR eC eKa A b) ≤
      4 * ((flatQ q k q : ℝ≥0∞) * prFindAvgK P hpk eG eJ eKR eC eKa A b) ^ (1 / 2 : ℝ) := by
  rw [prWinKEMSim_eq_prWin, prWinKEMK_eq_prWin']
  exact o2h_avg _

/-- The advantage of `A` in the game with simulated decapsulation. -/
def qINDCCAAdvantageSim (A : KEMQAdv m₁ m₂ n w q k c a PK C K) : ℝ≥0∞ :=
  absDiff (prWinKEMSim P hpk eG eJ eKR eC eKa A true) (prWinKEMSim P hpk eG eJ eKR eC eKa A false)

omit [DecidableEq M] [Fintype C] in
/-- The challenge-key hop:
`qINDCCAAdvantageSim A ≤ 8 √(q' · (prFindAvgK A true ⊔ prFindAvgK A false))`. -/
theorem hopK (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    qINDCCAAdvantageSim P hpk eG eJ eKR eC eKa A ≤
      8 * ((flatQ q k q : ℝ≥0∞) * (prFindAvgK P hpk eG eJ eKR eC eKa A true ⊔
        prFindAvgK P hpk eG eJ eKR eC eKa A false)) ^ (1 / 2 : ℝ) := by
  have key : ∀ b : Bool, absDiff (prWinKEMSim P hpk eG eJ eKR eC eKa A b)
      (prWinKEMK P hpk eG eJ eKR eC eKa A b) ≤
      4 * ((flatQ q k q : ℝ≥0∞) * (prFindAvgK P hpk eG eJ eKR eC eKa A true ⊔
        prFindAvgK P hpk eG eJ eKR eC eKa A false)) ^ (1 / 2 : ℝ) := by
    intro b
    refine (hopK_o2h P hpk eG eJ eKR eC eKa A b).trans ?_
    gcongr
    cases b
    · exact le_sup_right
    · exact le_sup_left
  calc qINDCCAAdvantageSim P hpk eG eJ eKR eC eKa A
      ≤ absDiff (prWinKEMSim P hpk eG eJ eKR eC eKa A true)
          (prWinKEMK P hpk eG eJ eKR eC eKa A true) +
        absDiff (prWinKEMK P hpk eG eJ eKR eC eKa A true)
          (prWinKEMSim P hpk eG eJ eKR eC eKa A false) := absDiff_triangle _ _ _
    _ ≤ 4 * ((flatQ q k q : ℝ≥0∞) * (prFindAvgK P hpk eG eJ eKR eC eKa A true ⊔
          prFindAvgK P hpk eG eJ eKR eC eKa A false)) ^ (1 / 2 : ℝ) +
        4 * ((flatQ q k q : ℝ≥0∞) * (prFindAvgK P hpk eG eJ eKR eC eKa A true ⊔
          prFindAvgK P hpk eG eJ eKR eC eKa A false)) ^ (1 / 2 : ℝ) := by
        refine add_le_add (key true) ?_
        rw [prWinKEMK_indep, absDiff_comm]
        exact key false
    _ = 8 * ((flatQ q k q : ℝ≥0∞) * (prFindAvgK P hpk eG eJ eKR eC eKa A true ⊔
          prFindAvgK P hpk eG eJ eKR eC eKa A false)) ^ (1 / 2 : ℝ) := by ring

omit [DecidableEq M] [Fintype C] in
/-- The averaged `Find` probability is at most four times the averaged
probability that the measured query of the plain run against the reprogrammed
oracle is the challenge point, summed over the queries. -/
theorem prFindAvgK_le (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prFindAvgK P hpk eG eJ eKR eC eKa A b ≤
      4 * ∑ j : Fin (flatQ q k q), ∑ p : KEMInput PK SK Z M K m₁ m₂ n × Fin n,
        (hopKGame P hpk eG eJ eKR eC eKa A b).sample p *
          guessProb ((hopKGame P hpk eG eJ eKR eC eKa A b).adv p)
            ((hopKGame P hpk eG eJ eKR eC eKa A b).oracle' p)
            ((hopKGame P hpk eG eJ eKR eC eKa A b).S p) j := by
  set G := hopKGame P hpk eG eJ eKR eC eKa A b with hG
  calc prFindAvgK P hpk eG eJ eKR eC eKa A b
      ≤ ∑ p, G.sample p * (4 * ∑ j, guessProb (G.adv p) (G.oracle' p) (G.S p) j) := by
        refine Finset.sum_le_sum fun p _ => ?_
        obtain ⟨ψ, hψ⟩ := G.pure p
        rw [prFind_congr _ _ _ _ (G.agree p) hψ]
        gcongr
        exact prFind_le_four_sum_guess _ _ _ hψ
    _ = 4 * ∑ j, ∑ p, G.sample p * guessProb (G.adv p) (G.oracle' p) (G.S p) j := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => by ring

end Game

end CatCrypt.Quantum.QROM
