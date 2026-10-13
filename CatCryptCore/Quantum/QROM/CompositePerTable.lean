/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.KEMOwcpaReduction

/-!
# The composed KEM game at a fixed `G`-table

The input weight `kemSample` of `Quantum/QROM/KEMQuantumGame.lean` is the
uniform weight on the `G`-table times a weight on the rest of the input that
does not read the `G`-table. The equality `prWinKEMHJ_eq_prWinKEMHq` of
`Quantum/QROM/KEMOwcpaReduction.lean` holds at every fixed `G`-table, key pair,
seed, challenge message and fake key, once the `J`-table is averaged.

## Main definitions

* `KEMRest` — the input without its `G`-table: key pair, seed, challenge
  message, fake key and `J`-table
* `kemJoin r G` — the input with rest `r` and `G`-table `G`
* `kemJoinEquiv` — `kemJoin` as an equivalence `KEMRest × (Fin m₁ → Fin n) ≃ KEMInput`
* `kemRestWeight P r` — the weight of the rest: `keygen` on the key pair, the
  rest uniform
* `winHJ A b i`, `winHq A b i` — the winning probabilities at an input of the
  games `prWinKEMHJ` and `prWinKEMHq`, averaged over `Hq`

## Main results

* `kemSample_kemJoin` — `kemSample P (kemJoin r G) = kemRestWeight P r * (n ^ m₁)⁻¹`
* `sum_kemSample_kemJoin` — a `kemSample`-weighted sum is a `kemRestWeight`-weighted
  sum of uniform averages over the `G`-table
* `prWinKEMHJ_eq_sum_winHJ`, `prWinKEMHq_eq_sum_winHq` — the two games as
  `kemSample`-weighted sums of `winHJ` and `winHq`
* `sum_J_winHJ_eq_winHq` — at a fixed `G`-table, key pair, seed, challenge
  message and fake key, the sums of `winHJ` and `winHq` over the `J`-table agree

## Scope

In `sum_J_winHJ_eq_winHq` the `J`-table is summed: in `winHJ` the decapsulation
answers off the image of the encryption map are the row `J(z, ·)`, in `winHq`
they are `Hq`, and the two agree only in law. The sum over `Hq` is inside
`winHJ` and `winHq`, and the sum over the table `T` reprogramming the row
`J(z, ·)` inside `winSimJ` and `winHq`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The input split at the `G`-table -/

section Split

variable {m₁ m₂ n : ℕ} {PK SK M C R K Z : Type}

/-- The input of the KEM game without its `G`-table: the key pair, the seed,
the challenge message, the fake key and the `J`-table. -/
abbrev KEMRest (PK SK Z M K : Type) (m₂ n : ℕ) : Type :=
  (PK × SK) × Z × M × K × (Fin m₂ → Fin n)

/-- The input with rest `r` and `G`-table `G`. -/
def kemJoin (r : KEMRest PK SK Z M K m₂ n) (G : Fin m₁ → Fin n) : KEMInput PK SK Z M K m₁ m₂ n :=
  (r.1, r.2.1, r.2.2.1, r.2.2.2.1, G, r.2.2.2.2)

/-- `kemJoin` as an equivalence between the rest paired with a `G`-table and
the input. -/
def kemJoinEquiv :
    KEMRest PK SK Z M K m₂ n × (Fin m₁ → Fin n) ≃ KEMInput PK SK Z M K m₁ m₂ n where
  toFun p := kemJoin p.1 p.2
  invFun i := ((i.1, i.2.1, i.2.2.1, i.2.2.2.1, i.2.2.2.2.2), i.2.2.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype PK] [Fintype SK] [Fintype M] [Fintype Z] [Fintype K]
  (P : Scheme PK SK M C R)

/-- The weight of the rest of an input: the key pair under `keygen`; the seed,
the message, the fake key and the `J`-table uniform. -/
def kemRestWeight (r : KEMRest PK SK Z M K m₂ n) : ℝ≥0∞ :=
  P.keygen r.1 * (Fintype.card Z : ℝ≥0∞)⁻¹ * (Fintype.card M : ℝ≥0∞)⁻¹ *
    (Fintype.card K : ℝ≥0∞)⁻¹ * ((n : ℝ≥0∞) ^ m₂)⁻¹

omit [Fintype PK] [Fintype SK] in
/-- The input weight is the rest weight times the uniform weight on the
`G`-table. -/
theorem kemSample_kemJoin (r : KEMRest PK SK Z M K m₂ n) (G : Fin m₁ → Fin n) :
    kemSample P (kemJoin r G) = kemRestWeight P r * ((n : ℝ≥0∞) ^ m₁)⁻¹ := by
  simp only [kemSample, kemJoin, kemRestWeight]
  ring

/-- A `kemSample`-weighted sum is a `kemRestWeight`-weighted sum of uniform
averages over the `G`-table. -/
theorem sum_kemSample_kemJoin (X : KEMInput PK SK Z M K m₁ m₂ n → ℝ≥0∞) :
    ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * X i =
      ∑ r : KEMRest PK SK Z M K m₂ n, kemRestWeight P r *
        ∑ G : Fin m₁ → Fin n, ((n : ℝ≥0∞) ^ m₁)⁻¹ * X (kemJoin r G) := by
  rw [← Fintype.sum_equiv kemJoinEquiv (fun p => kemSample P (kemJoin p.1 p.2) *
    X (kemJoin p.1 p.2)) _ fun _ => rfl, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun G _ => ?_
  rw [kemSample_kemJoin, mul_assoc]

end Split

/-! ## The composed game at a fixed `G`-table -/

section PerTable

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c]

/-- The winning probability of `prWinKEMHJ` at an input, averaged over `Hq`. -/
def winHJ (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (i : KEMInput PK SK Z M K m₁ m₂ n) : ℝ≥0∞ :=
  ∑ Hq : C → K, (Fintype.card (C → K) : ℝ≥0∞)⁻¹ *
    winSimJ P hpk eG eJ eKR eC eKa A b (inputH P hpk eG eKR i Hq)

/-- The winning probability of `prWinKEMHq` at an input, averaged over `Hq`
and the table `T`. -/
def winHq (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (i : KEMInput PK SK Z M K m₁ m₂ n) : ℝ≥0∞ :=
  ∑ Hq : C → K, (Fintype.card (C → K) : ℝ≥0∞)⁻¹ * ∑ T : C → Fin n, tabWeight n C *
    prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i)
        (if b then Hq (kemChal P hpk eG eKR i) else i.2.2.2.1))
      (kemOracle' eJ (inputH P hpk eG eKR i Hq) T) (decapsHq eC eKa Hq (kemChal P hpk eG eKR i))

omit [DecidableEq M] [Nonempty M] [Nonempty Z] [Fintype R] [Nonempty R] [NeZero c] in
theorem prWinKEMHJ_eq_sum_winHJ (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinKEMHJ P hpk eG eJ eKR eC eKa A b =
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * winHJ P hpk eG eJ eKR eC eKa A b i := by
  unfold prWinKEMHJ winHJ
  simp only [Finset.mul_sum, mul_assoc]

omit [DecidableEq M] [Nonempty M] [Nonempty Z] [Fintype R] [Nonempty R] [NeZero c] in
theorem prWinKEMHq_eq_sum_winHq (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinKEMHq P hpk eG eJ eKR eC eKa A b =
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * winHq P hpk eG eJ eKR eC eKa A b i := by
  unfold prWinKEMHq winHq
  simp only [Finset.mul_sum, mul_assoc]

omit [Fintype PK] [Fintype SK] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [Nonempty R] [NeZero c] in
open scoped Classical in
/-- At a fixed `G`-table, key pair, seed, challenge message and fake key, the
winning probabilities of `prWinKEMHJ` and `prWinKEMHq` summed over the
`J`-table agree. -/
theorem sum_J_winHJ_eq_winHq (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool)
    (ks : PK × SK) (z : Z) (ms : M) (kf : K) (G : Fin m₁ → Fin n) :
    ∑ J : Fin m₂ → Fin n, winHJ P hpk eG eJ eKR eC eKa A b (ks, z, ms, kf, G, J) =
      ∑ J : Fin m₂ → Fin n, winHq P hpk eG eJ eKR eC eKa A b (ks, z, ms, kf, G, J) := by
  obtain ⟨pk, sk⟩ := ks
  unfold winHJ winHq winSimJ
  simp only [kemChal_inputH, kemKey_inputH, decapsSim_inputH, Finset.mul_sum]
  simp only [kemChal, kemJ, kemOracle', kemJ', inputH, encOf, encAt, coinsOf, kemTab, kemG]
  set cs := P.enc pk ms (eKR.symm (G (eG (ms, hpk pk)))).2
  set κ := (Fintype.card (C → K) : ℝ≥0∞)⁻¹
  have hk : ∀ Hq Hq' : C → K,
      (∀ y, (∃ m', P.enc pk m' (eKR.symm (G (eG (m', hpk pk)))).2 = y) → Hq y = Hq' y) →
      keyHop (kemSlice hpk eG pk) (kemEncAt P eG pk) eKR.symm Hq G =
        keyHop (kemSlice hpk eG pk) (kemEncAt P eG pk) eKR.symm Hq' G := fun Hq Hq' h =>
    congrArg (fun i : KEMInput PK SK Z M K m₁ m₂ n => i.2.2.2.2.1)
      (inputH_congr P hpk eG eKR ((pk, sk), z, ms, kf, G, fun _ => 0) Hq Hq' h)
  exact sum_prefix_merge eJ eKR z
    (fun y => ∃ m', P.enc pk m' (eKR.symm (G (eG (m', hpk pk)))).2 = y)
    (fun Jo Hq H => κ * (tabWeight n C *
        prOutMR (A.run pk cs (if b = true then Hq cs else kf))
          (mergeOracle (keyHop (kemSlice hpk eG pk) (kemEncAt P eG pk) eKR.symm Hq G) Jo)
          (decapsHq eC eKa H cs)))
    (fun Jo Hq Hq' H h => by
      have hc : Hq cs = Hq' cs := h _ ⟨ms, rfl⟩
      rw [hc, hk Hq Hq' h])

end PerTable

end CatCrypt.Quantum.QROM
