/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.PRFBadTableKeyed
public import CatCryptCore.Crypto.MLKEM.FIPS203QROMQuantumMLWE

/-!
# The averaged KEM bound without a coin hypothesis

`qINDCCA_le_find_numeric_of_lam_coll` needs no coin hypothesis: at a key pair
with a message whose every coin fails to decrypt, the bound `hlam` on the
fraction of bad `G`-values forces the per-key failure bound `λ` to be at least
one, and that key pair is paid inside `Λ = E λ`. At `λ = lamSup` the bound
`hlam` holds by definition, so the only condition left on the scheme is a bound
on its coin-collision weight `collWeight` (`Quantum/QROM/CollisionWeight.lean`),
which enters `chainBound` linearly and is averaged over the table without a
bad-table term.

For the scheme with noise from a uniform table, the averaged collision weight is
at most `3 / |Sd|` plus the collision weight of `idealScheme`, and the failure
term is the one of `avg_keyAvg_lamSup_le_corrWorst`.

## Main results

* `qINDCCA_le_qOwcpaAux_numeric_of_lam_coll` — `qINDCCA_le_qOwcpaAux_numeric_coll`
  without the coin hypothesis
* `qINDCCA_le_chainBound_lam_coll`, `qINDCCA_le_chainBound_lamSup_coll` —
  `chainBound` at `Λ = keyAvg P lam` and `ε = collWeight P`
* `avg_qINDCCA_le_lamSup_coll` — the bound averaged over a table
* `avg_collWeight_prfScheme_le` — the averaged collision weight of `prfScheme` is
  at most `3 / |Sd|` plus the collision weight of `idealScheme`
* `avg_qINDCCAF_le_corrWorst_coll` — the averaged IND-CCA bound with the failure
  term at `corrWorst` and the collision term at `3 / |Sd| + collWeight` of
  `idealScheme`, and no condition on the table
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.QROM
open CatCrypt.Crypto.PKE.Games (Scheme)
open CatCrypt.Crypto.MLKEM.PRFOracle (avg avg_mono avg_add avg_sum prfRow)
open CatCrypt.Quantum.QROM.PRFChain (chainBound)
open CatCrypt.Crypto.MLKEM.MLKEM512FailureBound (sum_kemSample_mul_fst)
open CatCrypt.Crypto.MLKEM.PRFBadTableKeyed (keyAvg lamSup chainBound_mono_keyed idealScheme
  avg_keyAvg_lamSup_le_corrWorst)

noncomputable section

namespace CatCrypt.Crypto.MLKEM.PRFCoinWeak

/-! ## One scheme -/

section OneScheme

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c] [NeZero (m₁ + m₂)]

open scoped Classical in
/-- `qINDCCA_le_qOwcpaAux_numeric_coll` without the coin hypothesis: the quantum
IND-CCA advantage through the coin hop with every correctness term numeric in
`Λ = E λ`, each one-wayness term the winning probability of `owRedQuery A b`
in `qOwcpaAux`, and `ε` a bound on the coin-collision weight `collWeight P`. -/
theorem qINDCCA_le_qOwcpaAux_numeric_of_lam_coll [NeZero (flatQ q k q)]
    (A : KEMQAdv m₁ m₂ n w q k c a PK C K)
    (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk))
    (ε : ℝ≥0∞) (hcoll : collWeight P ≤ ε)
    (w₀ : ℕ) (hw : 2 * w = w₀ * ancDim (m₁ + m₂) n c)
    (Ans : PK → C → K → Fin a → Equiv.Perm ((Fin (m₁ + m₂) × Fin n) × Fin w₀))
    (hseg : ∀ pk cs κ j i, ((castMR hw (A.run pk cs κ)).seg j i : Matrix _ _ ℂ) *
        cleanProjM (m₁ + m₂) n w₀ c =
      cleanProjM (m₁ + m₂) n w₀ c * ((castMR hw (A.run pk cs κ)).seg j i : Matrix _ _ ℂ))
    (hrounds : ∀ pk cs κ j,
      (castMR hw (A.run pk cs κ)).rounds j = permRound (m₁ + m₂) n w₀ c (Ans pk cs κ))
    (hinit : ∀ pk cs κ,
      SupportedOn (cleanProjM (m₁ + m₂) n w₀ c) (castMR hw (A.run pk cs κ)).init.val) :
    qINDCCAAdvantage P hpk eG eJ eKR eC eKa A ≤
      (4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery A true) +
            ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
              (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)))) ^ (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
          (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 + ε) +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery A false) +
            ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
              (if i.2.2.1 ∈ kemGood P hpk eG eKR i then 0 else 1)))) ^ (1 / 2 : ℝ)) +
      2 * (8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ) +
          ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1) ^ (1 / 2 : ℝ))) :=
  qINDCCA_le_find_numeric_of_lam_coll P hpk eG eJ eKR eC eKa A lam hlam ε hcoll
    (fun b => qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery A b))
    (prFindCoin_le_qOwcpaAux P hpk eG eJ eKR eC eKa A) w₀ hw Ans hseg hrounds hinit

end OneScheme

section Keyed

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

variable [NeZero n] [NeZero c] [NeZero a] [NeZero (m₁ + m₂)] [NeZero (flatQ q k q)]

open scoped Classical in
/-- The quantum IND-CCA bound of one scheme at a key-dependent failure bound and
the coin-collision weight of the scheme: when the fraction of bad `G`-values at
every point is at most `lam` of the key pair, the advantage of `A` is at most
`chainBound` at `Λ = keyAvg P lam`, `ε = collWeight P` and the one-wayness
probabilities of `owRedQuery (nfKEM A) b`. -/
theorem qINDCCA_le_chainBound_lam_coll (P : Scheme PK SK M C R)
    (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (lam : PK × SK → ℝ≥0∞)
    (hlam : ∀ pk sk, P.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞) ≤ lam (pk, sk)) :
    qINDCCAAdvantage P hpk eG eJ eKR eC eKa A ≤
      chainBound (flatQ q k q) (flatQ (q + 4) k q) (keyAvg P lam) (collWeight P)
        (Fintype.card Z : ℝ≥0∞)⁻¹
        (qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery (nfKEM A) true))
        (qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery (nfKEM A) false)) := by
  rw [← qINDCCAAdvantage_nfKEM]
  refine (qINDCCA_le_qOwcpaAux_numeric_of_lam_coll P hpk eG eJ eKR eC eKa (nfKEM A) lam
    hlam (collWeight P) le_rfl (2 * (w * nfX c a k)) (nfKEM_hw w c a k (m₁ + m₂))
    (fun _ _ _ => nfAns (m₁ + m₂) n c a k w) (nfKEM_hseg A) (nfKEM_hrounds A)
    (nfKEM_hinit A)).trans ?_
  have hΛ := deltaStar_le_Lambda P hpk eG eKR (Z := Z) (m₂ := m₂) lam hlam
  have hsum : ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * lam i.1 = keyAvg P lam :=
    sum_kemSample_mul_fst P lam
  rw [hsum] at hΛ ⊢
  unfold chainBound
  gcongr

/-- `qINDCCA_le_chainBound_lam_coll` at `lamSup`, where the failure-bound hypothesis
holds by definition. -/
theorem qINDCCA_le_chainBound_lamSup_coll (P : Scheme PK SK M C R)
    (A : KEMQAdv m₁ m₂ n w q k c a PK C K) :
    qINDCCAAdvantage P hpk eG eJ eKR eC eKa A ≤
      chainBound (flatQ q k q) (flatQ (q + 4) k q) (keyAvg P (lamSup hpk eG eKR P))
        (collWeight P) (Fintype.card Z : ℝ≥0∞)⁻¹
        (qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery (nfKEM A) true))
        (qOwcpaAux P hpk eG eJ eKR eC eKa (owRedQuery (nfKEM A) false)) :=
  qINDCCA_le_chainBound_lam_coll hpk eG eJ eKR eC eKa P A _ fun pk sk _ x =>
    le_iSup (fun x : Fin m₁ =>
      ((badVals (kemBad P hpk eG eKR pk sk) x).card : ℝ≥0∞) / (n : ℝ≥0∞)) x

variable {T : Type} [Fintype T] [Nonempty T]

open scoped Classical in
/-- The quantum IND-CCA bound averaged over a table, with no condition on the
table: the average advantage is at most `chainBound` at the averages over `F` of
`keyAvg (P F) (lamSup …)`, of the coin-collision weight `collWeight (P F)` and of
the one-wayness probabilities. The collision weight enters `chainBound` linearly,
so the average is carried through it without a bad-table term. -/
theorem avg_qINDCCA_le_lamSup_coll (P : T → Scheme PK SK M C R)
    (A : T → KEMQAdv m₁ m₂ n w q k c a PK C K) :
    (avg fun F => qINDCCAAdvantage (P F) hpk eG eJ eKR eC eKa (A F)) ≤
      chainBound (flatQ q k q) (flatQ (q + 4) k q)
        (avg fun F => keyAvg (P F) (lamSup hpk eG eKR (P F))) (avg fun F => collWeight (P F))
        (Fintype.card Z : ℝ≥0∞)⁻¹
        (avg fun F => qOwcpaAux (P F) hpk eG eJ eKR eC eKa (owRedQuery (nfKEM (A F)) true))
        (avg fun F => qOwcpaAux (P F) hpk eG eJ eKR eC eKa (owRedQuery (nfKEM (A F)) false)) :=
  (avg_mono fun F => qINDCCA_le_chainBound_lamSup_coll hpk eG eJ eKR eC eKa (P F) (A F)).trans
    (CatCrypt.Quantum.QROM.PRFChain.avg_chainBound_all_le _ _ _ _ _ _ _)

end Keyed

/-! ## The coin-collision weight of the scheme with noise from the table -/

section Coll

open CatCrypt.Crypto.MLKEM.PRFOracle (prfRow setRows prfRow_setRows_of_ne avg_setRows avg_prod
  avg_comm avg_const avg_mul_left avg_diag)
open CatCrypt.Crypto.MLKEM.PRFAuxHop (prfScheme)
open CatCrypt.Crypto.MLKEM.PRFBadTable (rowEquiv rowEquiv_apply avg_equiv)
open CatCrypt.Crypto.MLKEM.PRFBadTableKeyed (avg_eval)
open CatCrypt.Crypto.MLKEM.PRFKEMChain (sum_map_uniform)

variable {Sd Nc PK SK M C KS Φ : Type} {m₃ n : ℕ}
  [Fintype Φ] [Nonempty Φ] [Fintype Sd] [DecidableEq Sd] [Nonempty Sd] [Fintype Nc]
  [DecidableEq Nc] [DecidableEq C] [Fintype PK] [DecidableEq PK] [Fintype SK] [DecidableEq SK]
  [Fintype M] [Nonempty M] [NeZero n]
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → PK × SK) (enc : PK → M → (Nc → Fin n) → C)
  (dec : SK → C → Option M) (eK : (Nc → Fin n) → KS)

omit [DecidableEq Sd] [Fintype Nc] [DecidableEq Nc] [Nonempty M] [NeZero n] in
/-- The coin-collision weight of `prfScheme F` as an average over the public coins,
the key seed and two coin seeds. -/
theorem collWeight_prfScheme (F : Fin m₃ → Fin n) :
    collWeight (prfScheme eD kg enc dec eK id F) =
      avg fun p : Φ × Sd => ∑ m : M, (Fintype.card M : ℝ≥0∞)⁻¹ *
        avg fun r : Sd => avg fun r' : Sd =>
          if enc (kg p.1 (eK (prfRow eD F p.2))).1 m (prfRow eD F r') =
              enc (kg p.1 (eK (prfRow eD F p.2))).1 m (prfRow eD F r) then (1 : ℝ≥0∞) else 0 := by
  rw [collWeight, tsum_fintype]
  change ∑ ks, ((PMF.uniformOfFintype (Φ × Sd)).map fun p =>
    PRFOracle.keygenPrf eD kg eK F p.1 p.2) ks * _ = _
  rw [sum_map_uniform]
  rfl

omit [Nonempty M] in
/-- The coin-collision weight of `idealScheme` as an average over the public coins,
the key-noise row and two encryption-noise rows. -/
theorem collWeight_idealScheme :
    collWeight (idealScheme kg enc dec eK) =
      avg fun p : Φ × (Nc → Fin n) => ∑ m : M, (Fintype.card M : ℝ≥0∞)⁻¹ *
        avg fun w : Nc → Fin n => avg fun w' : Nc → Fin n =>
          if enc (kg p.1 (eK p.2)).1 m w' = enc (kg p.1 (eK p.2)).1 m w then (1 : ℝ≥0∞) else 0 := by
  rw [collWeight, tsum_fintype]
  change ∑ ks, ((PMF.uniformOfFintype (Φ × (Nc → Fin n))).map fun p => kg p.1 (eK p.2)) ks * _ = _
  rw [sum_map_uniform]
  rfl

omit [Fintype Φ] [Nonempty Φ] [Nonempty Sd] [Fintype PK] [DecidableEq PK] [Fintype SK]
  [DecidableEq SK] [Fintype M] [Nonempty M] in
/-- At three distinct seeds, the rows of a uniform table are three independent
uniform rows: the collision indicator of `prfScheme F` at the key seed `σ` and the
coin seeds `r`, `r'` averages over `F` to the collision indicator of `idealScheme`
averaged over a key-noise row and two encryption-noise rows. -/
theorem avg_rows_eq_ideal (φ : Φ) (m : M) {σ r r' : Sd} (hσr : σ ≠ r) (hσr' : σ ≠ r')
    (hrr' : r ≠ r') :
    (avg fun F : Fin m₃ → Fin n =>
        if enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r') =
            enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r) then (1 : ℝ≥0∞) else 0) =
      avg fun v : Nc → Fin n => avg fun w : Nc → Fin n => avg fun w' : Nc → Fin n =>
        if enc (kg φ (eK v)).1 m w' = enc (kg φ (eK v)).1 m w then (1 : ℝ≥0∞) else 0 := by
  have h := avg_setRows eD hrr' (fun (a b : Nc → Fin n) (F : Fin m₃ → Fin n) =>
    if enc (kg φ (eK (prfRow eD F σ))).1 m b = enc (kg φ (eK (prfRow eD F σ))).1 m a
      then (1 : ℝ≥0∞) else 0)
  simp only [prfRow_setRows_of_ne eD _ hσr hσr'] at h
  rw [← h]
  simp only [avg_prod]
  have hrow : ∀ a b : Nc → Fin n, (avg fun F : Fin m₃ → Fin n =>
      if enc (kg φ (eK (prfRow eD F σ))).1 m b = enc (kg φ (eK (prfRow eD F σ))).1 m a
        then (1 : ℝ≥0∞) else 0) =
      avg fun v : Nc → Fin n =>
        if enc (kg φ (eK v)).1 m b = enc (kg φ (eK v)).1 m a then (1 : ℝ≥0∞) else 0 := by
    intro a b
    rw [show (fun F : Fin m₃ → Fin n =>
        if enc (kg φ (eK (prfRow eD F σ))).1 m b = enc (kg φ (eK (prfRow eD F σ))).1 m a
          then (1 : ℝ≥0∞) else 0) =
        fun F => (fun G : Sd → Nc → Fin n =>
          if enc (kg φ (eK (G σ))).1 m b = enc (kg φ (eK (G σ))).1 m a then (1 : ℝ≥0∞) else 0)
          (rowEquiv eD F) from rfl, avg_equiv (rowEquiv eD) (fun G : Sd → Nc → Fin n =>
          if enc (kg φ (eK (G σ))).1 m b = enc (kg φ (eK (G σ))).1 m a then (1 : ℝ≥0∞) else 0),
      avg_eval σ (fun v : Nc → Fin n =>
        if enc (kg φ (eK v)).1 m b = enc (kg φ (eK v)).1 m a then (1 : ℝ≥0∞) else 0)]
  simp only [hrow]
  have h1 : ∀ a : Nc → Fin n, (avg fun b : Nc → Fin n => avg fun v : Nc → Fin n =>
      if enc (kg φ (eK v)).1 m b = enc (kg φ (eK v)).1 m a then (1 : ℝ≥0∞) else 0) =
      avg fun v : Nc → Fin n => avg fun b : Nc → Fin n =>
        if enc (kg φ (eK v)).1 m b = enc (kg φ (eK v)).1 m a then (1 : ℝ≥0∞) else 0 :=
    fun a => avg_comm _
  simp only [h1]
  exact avg_comm _

omit [DecidableEq Sd] [Nonempty Sd] [NeZero n] in
/-- The average over the table commutes past the three seed averages. -/
theorem avg_table_seeds_comm (h : (Fin m₃ → Fin n) → Sd → Sd → Sd → ℝ≥0∞) :
    (avg fun F => avg fun σ => avg fun r => avg fun r' => h F σ r r') =
      avg fun σ => avg fun r => avg fun r' => avg fun F => h F σ r r' := by
  rw [avg_comm (fun F σ => avg fun r => avg fun r' => h F σ r r')]
  refine congrArg avg (funext fun σ => ?_)
  rw [avg_comm (fun F r => avg fun r' => h F σ r r')]
  refine congrArg avg (funext fun r => ?_)
  exact avg_comm _

omit [Fintype Φ] [Nonempty Φ] [Fintype PK] [DecidableEq PK] [Fintype SK] [DecidableEq SK]
  [Fintype M] [Nonempty M] in
/-- The collision indicator of `prfScheme F` at the key seed `σ` and the coin seeds
`r`, `r'`, averaged over the table and the three seeds, is at most `3 / |Sd|` (the
seeds are not distinct) plus the collision indicator of `idealScheme` averaged over
a key-noise row and two encryption-noise rows. -/
theorem avg_coll_rows_le (φ : Φ) (m : M) :
    (avg fun F : Fin m₃ → Fin n => avg fun σ : Sd => avg fun r : Sd => avg fun r' : Sd =>
        if enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r') =
            enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r) then (1 : ℝ≥0∞) else 0) ≤
      3 * (Fintype.card Sd : ℝ≥0∞)⁻¹ +
        avg fun v : Nc → Fin n => avg fun w : Nc → Fin n => avg fun w' : Nc → Fin n =>
          if enc (kg φ (eK v)).1 m w' = enc (kg φ (eK v)).1 m w then (1 : ℝ≥0∞) else 0 := by
  have hpt : ∀ (F : Fin m₃ → Fin n) (σ r r' : Sd),
      (if enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r') =
          enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r) then (1 : ℝ≥0∞) else 0) ≤
        (if σ = r then 1 else 0) + (if σ = r' then 1 else 0) + (if r = r' then 1 else 0) +
          (if σ ≠ r ∧ σ ≠ r' ∧ r ≠ r' then
            (if enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r') =
              enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r) then (1 : ℝ≥0∞) else 0)
          else 0) := by
    intro F σ r r'
    by_cases hD : σ ≠ r ∧ σ ≠ r' ∧ r ≠ r'
    · rw [if_pos hD]
      exact le_add_self
    · rw [if_neg hD, add_zero]
      refine le_trans (by split_ifs <;> simp) (?_ : (1 : ℝ≥0∞) ≤ _)
      simp only [not_and, not_not] at hD
      by_cases h1 : σ = r
      · rw [if_pos h1]
        exact le_add_right (le_add_right le_rfl)
      by_cases h2 : σ = r'
      · rw [if_pos h2]
        exact le_add_right (le_add_left le_rfl)
      rw [if_pos (hD h1 h2)]
      exact le_add_left le_rfl
  have hdiag : (avg fun σ : Sd => avg fun r : Sd => if σ = r then (1 : ℝ≥0∞) else 0) =
      (Fintype.card Sd : ℝ≥0∞)⁻¹ := by
    have hd := avg_diag (α := Sd)
    rw [avg_prod] at hd
    exact hd
  have hD : ∀ σ r r' : Sd, (avg fun F : Fin m₃ → Fin n =>
      if σ ≠ r ∧ σ ≠ r' ∧ r ≠ r' then
        (if enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r') =
          enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r) then (1 : ℝ≥0∞) else 0)
      else 0) ≤
      avg fun v : Nc → Fin n => avg fun w : Nc → Fin n => avg fun w' : Nc → Fin n =>
        if enc (kg φ (eK v)).1 m w' = enc (kg φ (eK v)).1 m w then (1 : ℝ≥0∞) else 0 := by
    intro σ r r'
    by_cases hd : σ ≠ r ∧ σ ≠ r' ∧ r ≠ r'
    · simp only [if_pos hd]
      exact (avg_rows_eq_ideal eD kg enc eK φ m hd.1 hd.2.1 hd.2.2).le
    · simp only [if_neg hd, avg_const]
      exact zero_le
  calc _ ≤ avg fun F : Fin m₃ → Fin n => avg fun σ : Sd => avg fun r : Sd => avg fun r' : Sd =>
        (if σ = r then (1 : ℝ≥0∞) else 0) + (if σ = r' then 1 else 0) + (if r = r' then 1 else 0) +
          (if σ ≠ r ∧ σ ≠ r' ∧ r ≠ r' then
            (if enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r') =
              enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r) then (1 : ℝ≥0∞) else 0)
          else 0) :=
        avg_mono fun F => avg_mono fun σ => avg_mono fun r => avg_mono fun r' => hpt F σ r r'
    _ = (Fintype.card Sd : ℝ≥0∞)⁻¹ + (Fintype.card Sd : ℝ≥0∞)⁻¹ + (Fintype.card Sd : ℝ≥0∞)⁻¹ +
        avg fun σ : Sd => avg fun r : Sd => avg fun r' : Sd => avg fun F : Fin m₃ → Fin n =>
          if σ ≠ r ∧ σ ≠ r' ∧ r ≠ r' then
            (if enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r') =
              enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r) then (1 : ℝ≥0∞) else 0)
          else 0 := by
        simp only [avg_add, avg_const, hdiag, avg_table_seeds_comm]
    _ ≤ (Fintype.card Sd : ℝ≥0∞)⁻¹ + (Fintype.card Sd : ℝ≥0∞)⁻¹ + (Fintype.card Sd : ℝ≥0∞)⁻¹ +
        avg fun v : Nc → Fin n => avg fun w : Nc → Fin n => avg fun w' : Nc → Fin n =>
          if enc (kg φ (eK v)).1 m w' = enc (kg φ (eK v)).1 m w then (1 : ℝ≥0∞) else 0 := by
        gcongr
        exact (avg_mono fun σ => avg_mono fun r => avg_mono fun r' => hD σ r r').trans
          (by simp only [avg_const]; exact le_rfl)
    _ = _ := by ring

/-- **The averaged coin-collision weight of the scheme with noise from the table.**
The average over a uniform table `F` of `collWeight (prfScheme F)` is at most
`3 / |Sd|`, the weight of the draws at which the key seed and the two coin seeds
are not distinct, plus the coin-collision weight of `idealScheme`. -/
theorem avg_collWeight_prfScheme_le :
    (avg fun F : Fin m₃ → Fin n => collWeight (prfScheme eD kg enc dec eK id F)) ≤
      3 * (Fintype.card Sd : ℝ≥0∞)⁻¹ + collWeight (idealScheme kg enc dec eK) := by
  simp only [collWeight_prfScheme, collWeight_idealScheme, avg_prod, avg_sum, avg_mul_left]
  have hm : ∀ m : M, (avg fun F : Fin m₃ → Fin n => avg fun φ : Φ => avg fun σ : Sd =>
      avg fun r : Sd => avg fun r' : Sd =>
        if enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r') =
            enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r) then (1 : ℝ≥0∞) else 0) ≤
      3 * (Fintype.card Sd : ℝ≥0∞)⁻¹ +
        avg fun φ : Φ => avg fun v : Nc → Fin n => avg fun w : Nc → Fin n =>
          avg fun w' : Nc → Fin n =>
            if enc (kg φ (eK v)).1 m w' = enc (kg φ (eK v)).1 m w then (1 : ℝ≥0∞) else 0 := by
    intro m
    rw [avg_comm (fun (F : Fin m₃ → Fin n) (φ : Φ) => avg fun σ : Sd => avg fun r : Sd =>
      avg fun r' : Sd =>
        if enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r') =
            enc (kg φ (eK (prfRow eD F σ))).1 m (prfRow eD F r) then (1 : ℝ≥0∞) else 0)]
    refine (avg_mono fun φ => avg_coll_rows_le eD kg enc eK φ m).trans ?_
    rw [avg_add, avg_const]
  calc _ ≤ ∑ m : M, (Fintype.card M : ℝ≥0∞)⁻¹ * (3 * (Fintype.card Sd : ℝ≥0∞)⁻¹ +
        avg fun φ : Φ => avg fun v : Nc → Fin n => avg fun w : Nc → Fin n =>
          avg fun w' : Nc → Fin n =>
            if enc (kg φ (eK v)).1 m w' = enc (kg φ (eK v)).1 m w then (1 : ℝ≥0∞) else 0) :=
        Finset.sum_le_sum fun m _ => mul_le_mul_right (hm m) _
    _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, sum_inv_card M, one_mul]

end Coll

/-! ## The averaged bound with the collision weight of the scheme with uniform noise rows -/

section IdealColl

open CatCrypt.Crypto.MLKEM.PRFAuxHop (prfScheme)
open CatCrypt.Crypto.MLKEM.PRFKEMChain (qINDCCAAdvantageF qINDCCAAdvantage_hardwire owTerm
  avg_qOwcpaAux_le_owTerm)
open CatCrypt.Quantum.QROM.PRFAdvEmbed (hardwire)
open CatCrypt.Quantum.QROM.PRFChain (chainBound_mono_all)

variable {Sd Nc PK SK M C KS K Hash Z Φ : Type} {m₁ m₂ m₃ n w q k c a : ℕ}
  [Fintype Φ] [Nonempty Φ] [Fintype Sd] [DecidableEq Sd] [Nonempty Sd] [Fintype Nc]
  [DecidableEq Nc] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype C] [DecidableEq C]
  [Fintype K] [Nonempty K] [DecidableEq Hash] [Fintype PK] [DecidableEq PK] [Fintype SK]
  [DecidableEq SK] [Fintype M] [DecidableEq M] [Nonempty M]
  [NeZero n] [NeZero c] [NeZero a] [NeZero (m₁ + m₂)] [NeZero (flatQ q k q)]
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → PK × SK) (enc : PK → M → (Nc → Fin n) → C)
  (dec : SK → C → Option M) (eK : (Nc → Fin n) → KS)
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × Sd) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

open scoped Classical in
/-- **The quantum IND-CCA bound over the noise table at the correctness error and
the coin-collision weight of the scheme with uniform noise rows, with no condition
on the table.** For every KEM adversary `A` whose oracle also answers the table
`F`, the IND-CCA advantage averaged over `F` is at most `chainBound` at the
failure term `6 · corrWorst + (t + 2) / N + |M| · 2⁻ᵗ`, the collision term
`3 / N + collWeight idealScheme`, and `owTerm true`, `owTerm false`, where
`corrWorst` and `collWeight` are those of `idealScheme` and `N = |Sd|`. -/
theorem avg_qINDCCAF_le_corrWorst_coll (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (t : ℕ) :
    (avg fun F : Fin m₃ → Fin n =>
      qINDCCAAdvantageF (prfScheme eD kg enc dec eK id F) hpk eG eJ eKR eC eKa F A) ≤
      chainBound (flatQ q k q) (flatQ (q + 4) k q)
        (6 * (idealScheme kg enc dec eK).corrWorst +
          ((t + 2 : ℕ) : ℝ≥0∞) / Fintype.card Sd + (Fintype.card M : ℝ≥0∞) * 2⁻¹ ^ t)
        (3 * (Fintype.card Sd : ℝ≥0∞)⁻¹ + collWeight (idealScheme kg enc dec eK))
        (Fintype.card Z : ℝ≥0∞)⁻¹
        (owTerm eD kg enc dec eK hpk eG eJ eKR eC eKa A true)
        (owTerm eD kg enc dec eK hpk eG eJ eKR eC eKa A false) := by
  simp only [← qINDCCAAdvantage_hardwire]
  refine (avg_qINDCCA_le_lamSup_coll hpk eG eJ eKR eC eKa
    (fun F => prfScheme eD kg enc dec eK id F) (fun F => hardwire F A)).trans ?_
  exact chainBound_mono_all _ _ _ (avg_keyAvg_lamSup_le_corrWorst eD kg enc dec eK hpk eG eKR t)
    (avg_collWeight_prfScheme_le eD kg enc dec eK)
    (avg_qOwcpaAux_le_owTerm eD kg enc dec eK hpk eG eJ eKR eC eKa A true)
    (avg_qOwcpaAux_le_owTerm eD kg enc dec eK hpk eG eJ eKR eC eKa A false)

end IdealColl

end CatCrypt.Crypto.MLKEM.PRFCoinWeak

end

end
