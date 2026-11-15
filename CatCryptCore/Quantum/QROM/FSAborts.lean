/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.MRGenFinalH
public import CatCryptCore.Quantum.QROM.RecordRounds
public import CatCryptCore.Quantum.QROM.RecordRoundsFinal
public import CatCryptCore.Quantum.QROM.RoundOracleDep
public import CatCryptCore.Crypto.FiatShamirROM.StatHVZK

/-!
# Fiat–Shamir with aborts as a signature scheme with a hash

`fsAbortSig P κ Msg recom` is Fiat–Shamir with aborts over a core Σ-protocol `P`
(`FiatShamirROM.Sigma`, with its acceptance test `accept`), as a `QROMSig`: the secret key is
the statement–witness pair, the signer's coins are `κ` prover randomnesses, attempt `i`
commits `a_i`, reads the challenge `H (μ, a_i)` and responds `z_i`, and the signature is the
pair `(H (μ, a_i), z_i)` of the first attempt whose response is accepted, or `none` when all
`κ` attempts are rejected. Verification recovers the commitment with `recom` and reads the
hash at `(μ, recom x e z)`.

The simulation of the signer at fresh challenges is exact under zero HVZK distance at the
pair (`fsAborts_attempts_sim_eq`): the output of the `κ`-attempt signer, run with fresh
uniform challenges, has the law of the `κ`-attempt simulator. The per-attempt statement
`hvzkDistAt x w = 0` (`Sigma.StatHVZKAt`) quantifies over tests that do not read the
commitment of a rejected transcript; the view of an attempt (`attemptView`) is such a test,
since a rejected attempt shows only that it was rejected. The laws of one attempt therefore
agree (`attemptView_law_eq`), including the probability of rejection, and the `κ`-attempt
output is a function of `κ` independent attempt views (`avg_firstSome_eq`). The number of
rejected attempts is visible only through the event that all `κ` attempts are rejected (the
signature `none`), whose probability is a product of rejection probabilities; no law beyond
the per-attempt one is needed.

## The CMA-to-NMA step in the QROM and BBD+23

The hop sequence for the quantum EUF-CMA game (`qEUFCMAAdvantage`) programs the oracle once,
before the run, at all `κ` attempt points of every message, executed or not: G0 the real game;
G0* the oracle overwritten at all attempt points by fresh challenges, the signer reading it,
equal to G0 (`fsG0_eq_fsG0s`); G1 the signer of each pair reading its own challenges (a
classical bad event on colliding attempt commitments); the bad event of a forgery at an accepted
point, charged in G1, where the oracle is uniform; G2 the oracle programmed at the accepted
points only, the values at the other attempt points fresh (`fsG1nb_fsG2_le`, gentle resampling
with the forgery test as one extra query); G3 the signer replaced by the simulator, exactly
(`fsG2_eq_fsG3`); G3 is the no-message advantage of the reduction `fsNMA`
(`fsG3_eq_qNMAProgAdvantage`), which has plain access to the oracle: it samples the simulator
coins, answers the rounds with the simulated signatures, and routes its queries (`routeAdv`). A
query at a programmed point is swapped into a saved register, the query to `H` acts on the
state `|0⟩ ⊗ |+⟩` of an ancilla, which every query leaves fixed, and the programmed value is
added; the routed run against `H` is the run against the programmed oracle (`prOut_routeAdv`).

Barbosa, Barthe, Doczkal, Don, Fehr, Grégoire, Huang, Hülsing, Lee and Wu (CRYPTO 2023,
"Fixing and mechanizing the security proof of Fiat–Shamir with aborts and Dilithium")
locate the gap of the earlier CMA-to-NMA proof at the rejected attempts: their commitments
are not output by the simulator, and the oracle values at those points must be accounted for
separately. They program adaptively inside each signing query and show that accepted
transcripts are independent of the rejected commitments. In the sequence above, G1 to G2
charges the rejected points. The pair whose `κ` attempts are all rejected (signature `none`)
reveals that its commitments were rejected, so the resampling term uses the guessing
probability of a commitment given rejection together with the unconditional one. The
forgery-point event is charged in G1: charged in G3, the acceptance test biases the oracle at
the programmed points, which is the gap BBD+23 identify.

## Main definitions

* `fsAttempt`, `fsSimAttempt` — one honest attempt at a challenge, and one simulated attempt
* `firstSome` — the first defined entry of a vector of attempts
* `fsAbortSig` — Fiat–Shamir with aborts as a `QROMSig`
* `attemptView` — the view of one attempt: the transcript if accepted, nothing otherwise
* `Sigma.rejCommitDistAt` — the guessing probability of the commitment given rejection
* `nonAccCom` — the commitments of the attempts other than the accepted one
* `reprog` — a table overwritten at a list of points, the first index winning
* `matchAt`, `prog1`, `prog2` — a table programmed at entries and at rows of entries
* `pairOut`, `pairsOut`, `pairSimOut` — the outputs of the honest and simulated pairs
* `attRows`, `accRow`, `outTab`, `nonAccPts` — the attempt entries, the accepted entries, the
  signing table of the outputs and the points of the attempts other than the accepted ones
* `prWinProg`, `notAccFinal`, `winAdv` — the winning probability at a signing table and an
  oracle with an extra final condition, the forgeries outside the accepted points, and the
  corresponding adversary without rounds
* `attCol` — a collision of the attempt points of a pair with those of the pairs of its message
* `fsG0s`, `fsG1`, `fsG1nb`, `fsProgWin`, `fsG2`, `fsG3` — the games of the CMA-to-NMA step
  at a key
* `progOracle`, `routeAdv`, `routeAncState` — an oracle programmed by a partial table, and an
  adversary run against the programmed oracle with plain access to the oracle
* `QNMAAdv`, `nmaTest`, `prNMA`, `qNMAProgAdvantage` — no-message adversaries, their winning
  test and probability, and the no-message advantage of a randomized one
* `accTab`, `fsNMA` — the table of the programmed oracle of G3 and the no-message reduction

## Main results

* `fsAbortSig_verifyH` — verification reads the hash at the recovered commitment
* `attemptView_law_eq` — under zero HVZK distance at the pair, the honest and the simulated
  attempt views have the same law at every challenge
* `avg_firstSome_eq` — attempt laws that agree give `κ`-attempt outputs that agree
* `fsAborts_attempts_sim_eq` — the `κ`-attempt signer at fresh challenges has the law of the
  `κ`-attempt simulator
* `avg_pi_eq`, `fsAborts_pairs_sim_eq` — independent coordinates with equal one-coordinate
  laws give equal averages of every function of all coordinates; the signers of all pairs have
  the law of the simulators
* `sum_reprog_eq` — a uniform table overwritten at points by fresh uniform values is uniform,
  for every choice of the points
* `rejected_mem_cond_le` — given the output of `κ` attempts, a commitment `a` is among the
  commitments of the attempts other than the accepted one with probability at most
  `κ (rejCommitDistAt ⊔ commitDistAt)`
* `sum_prog2_eq` — the same for rows of points
* `fsG0_eq_fsG0s` — G0 = G0*
* `prog2_attRows_eq_prog1_accRow` — the oracles of G1 and G2 agree outside `nonAccPts`
* `sum_pairsOut_nonAccPts_le` — given the outputs of all pairs, a point lies in `nonAccPts`
  with probability at most `T κ (rejCommitDistAt ⊔ commitDistAt)`
* `fsG1nb_fsG2_le` — G1 to G2 on the forgeries outside the accepted points, with the term
  `2 (flatQ q k q + 1) √(T κ (rejCommitDistAt ⊔ commitDistAt))`
* `fsG2_eq_fsG3` — G2 = G3 under zero HVZK distance at the key
* `sum_attCol_le` — given the prover randomness of the other pairs, a collision of attempt points
  at a pair has probability at most `T κ² ε`, `ε = commitDistAt`
* `sum_prog2_attRows_eq` — the prover randomness and the oracle of G0* are independent and
  uniform
* `fsG0s_fsG1_le` — G0* to G1, with the term `k T κ² ε`
* `prog2_split`, `sum_prog2_sel_eq`, `sum_sum_merge_eq` — programming at rows with disjoint
  points splits into two programmings; programming fresh values at selected rows keeps a table
  uniform; merging the coordinates of two independent vectors keeps the joint law
* `prOut_le_one`, `prOut_withFinalB_false`, `prOut_withFinalB_eq_sum` — bounds and finite
  additivity of diagonal final tests
* `sum_rand_mul_prog2_attRows_eq` — the prover randomness of a pair of the message `μ` is
  independent of the oracle of G0* and of the coins of the pairs of the other messages
* `fsG1_le_fsG1nb_add` — the bad event of G1, a forgery at an accepted point, has probability
  at most `T κ ε`
* `prOut_routeAdv`, `routeAdv_withFinalB` — the routed adversary against `H` accepts with the
  probability of the adversary against the programmed oracle, for every final test
* `fsG3_eq_qNMAProgAdvantage` — G3 is the no-message advantage of `fsNMA`
* `fsAborts_qcma_to_nma_at`, `fsAborts_qcma_to_nma` — CMA to NMA, per key and averaged over the
  keys: the advantage is at most that of `fsNMA` plus
  `min 1 (k T κ² ε + T κ ε + 2 (flatQ q k q + 1) √(T κ (ρ ⊔ ε)))`

## References

* [Kiltz, Lyubashevsky, Schaffner — A Concrete Treatment of Fiat–Shamir Signatures in the
  Quantum Random-Oracle Model, EUROCRYPT 2018]
* [Barbosa et al. — Fixing and mechanizing the security proof of Fiat–Shamir with aborts and
  Dilithium, CRYPTO 2023]
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace CatCrypt.Crypto.FiatShamirROM.Sigma

variable (P : Sigma)

/-- The guessing probability of the commitment given rejection at the pair `(x, w)`: the
    largest fraction, among the prover randomness–challenge pairs whose response is rejected,
    of those with a given commitment `a`; `0` when no response is rejected. -/
def rejCommitDistAt (x : P.Stmt) (w : P.Wit) : ℝ≥0∞ :=
  ⨆ a : P.Com,
    (∑ u : P.Rand × P.Ch, if P.accept (P.respond x w u.1 u.2) = false ∧ P.commit x w u.1 = a
      then (1 : ℝ≥0∞) else 0) /
    ∑ u : P.Rand × P.Ch, if P.accept (P.respond x w u.1 u.2) = false then (1 : ℝ≥0∞) else 0

/-- The number of rejected prover randomness–challenge pairs with commitment `a` is at most
    `rejCommitDistAt` times the number of rejected pairs. -/
theorem sum_rej_commit_le (x : P.Stmt) (w : P.Wit) (a : P.Com) :
    (∑ u : P.Rand × P.Ch, if P.accept (P.respond x w u.1 u.2) = false ∧ P.commit x w u.1 = a
      then (1 : ℝ≥0∞) else 0) ≤
      P.rejCommitDistAt x w *
        ∑ u : P.Rand × P.Ch,
          if P.accept (P.respond x w u.1 u.2) = false then (1 : ℝ≥0∞) else 0 := by
  set N := ∑ u : P.Rand × P.Ch, if P.accept (P.respond x w u.1 u.2) = false ∧
    P.commit x w u.1 = a then (1 : ℝ≥0∞) else 0 with hN
  set D := ∑ u : P.Rand × P.Ch, if P.accept (P.respond x w u.1 u.2) = false
    then (1 : ℝ≥0∞) else 0 with hD
  have hND : N ≤ D := Finset.sum_le_sum fun u _ => by split_ifs <;> simp_all
  by_cases hD0 : D = 0
  · rw [hD0] at hND ⊢
    simpa using hND
  · have hDt : D ≠ ⊤ := ENNReal.sum_ne_top.mpr fun u _ => by split_ifs <;> simp
    calc N = N / D * D := (ENNReal.div_mul_cancel hD0 hDt).symm
      _ ≤ P.rejCommitDistAt x w * D := by
        gcongr
        exact le_iSup (fun a : P.Com => (∑ u : P.Rand × P.Ch,
          if P.accept (P.respond x w u.1 u.2) = false ∧ P.commit x w u.1 = a
            then (1 : ℝ≥0∞) else 0) / D) a

/-- The number of prover randomness–challenge pairs with commitment `a` is at most
    `commitDistAt` times the number of pairs. -/
theorem sum_commit_le (x : P.Stmt) (w : P.Wit) (a : P.Com) :
    (∑ u : P.Rand × P.Ch, if P.commit x w u.1 = a then (1 : ℝ≥0∞) else 0) ≤
      P.commitDistAt x w * ∑ _u : P.Rand × P.Ch, (1 : ℝ≥0∞) := by
  have h1 : (PMF.uniformFintype P.Rand).toOuterMeasure {r | P.commit x w r = a} =
      (∑ r : P.Rand, if P.commit x w r = a then (1 : ℝ≥0∞) else 0) *
        (Fintype.card P.Rand : ℝ≥0∞)⁻¹ := by
    rw [PMF.toOuterMeasure_apply, tsum_fintype, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [Set.indicator_apply]
  have h2 : (∑ r : P.Rand, if P.commit x w r = a then (1 : ℝ≥0∞) else 0) ≤
      P.commitDistAt x w * Fintype.card P.Rand := by
    calc (∑ r : P.Rand, if P.commit x w r = a then (1 : ℝ≥0∞) else 0)
        = ((∑ r : P.Rand, if P.commit x w r = a then (1 : ℝ≥0∞) else 0) *
            (Fintype.card P.Rand : ℝ≥0∞)⁻¹) * Fintype.card P.Rand := by
          rw [mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
      _ ≤ P.commitDistAt x w * Fintype.card P.Rand := by
          gcongr
          rw [← h1]
          exact le_iSup (fun a : P.Com =>
            (PMF.uniformFintype P.Rand).toOuterMeasure {r | P.commit x w r = a}) a
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  calc _ = (∑ r : P.Rand, if P.commit x w r = a then (1 : ℝ≥0∞) else 0) *
        Fintype.card P.Ch := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun r _ => by split_ifs <;> simp
    _ ≤ _ := by rw [← mul_assoc]; gcongr

end CatCrypt.Crypto.FiatShamirROM.Sigma

namespace CatCrypt.Quantum.QROM

open CatCrypt.Crypto.FiatShamirROM

/-! ## Attempts and the first accepted attempt -/

section FirstSome

variable {β : Type}

/-- The first defined entry of a vector of attempt outcomes, `none` if every entry is
    `none`. -/
def firstSome : {κ : ℕ} → (Fin κ → Option β) → Option β
  | 0, _ => none
  | _ + 1, v => (v 0).or (firstSome (Fin.tail v))

/-- `firstSome` of a vector with first entry `o` and tail `v`. -/
theorem firstSome_cons {κ : ℕ} (o : Option β) (v : Fin κ → Option β) :
    firstSome (Fin.cons o v : Fin (κ + 1) → Option β) = o.or (firstSome v) := by
  simp [firstSome]

/-- The uniform average over vectors of length `κ + 1` is the average over the first entry
    of the average over the tail. -/
theorem avg_fin_succ {α : Type} [Fintype α] {κ : ℕ} (f : (Fin (κ + 1) → α) → ℝ≥0∞) :
    ∑ v, (Fintype.card (Fin (κ + 1) → α) : ℝ≥0∞)⁻¹ * f v =
      ∑ a, (Fintype.card α : ℝ≥0∞)⁻¹ *
        ∑ v, (Fintype.card (Fin κ → α) : ℝ≥0∞)⁻¹ * f (Fin.cons a v) := by
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  have hc : (Fintype.card (Fin (κ + 1) → α) : ℝ≥0∞)⁻¹ =
      (Fintype.card α : ℝ≥0∞)⁻¹ * (Fintype.card (Fin κ → α) : ℝ≥0∞)⁻¹ := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_succ',
      Nat.cast_mul, ENNReal.mul_inv (by simp) (by simp)]
  simp only [hc, Finset.mul_sum, mul_assoc]
  rfl

/-- Two attempt laws with the same averages give `κ`-attempt outputs with the same
    averages: the output `firstSome` of `κ` independent attempts depends only on the law of
    one attempt. -/
theorem avg_firstSome_eq {α α' : Type} [Fintype α] [Fintype α'] (att : α → Option β)
    (att' : α' → Option β)
    (h : ∀ g : Option β → ℝ≥0∞, ∑ a, (Fintype.card α : ℝ≥0∞)⁻¹ * g (att a) =
      ∑ a, (Fintype.card α' : ℝ≥0∞)⁻¹ * g (att' a)) :
    ∀ (κ : ℕ) (g : Option β → ℝ≥0∞),
      ∑ u : Fin κ → α, (Fintype.card (Fin κ → α) : ℝ≥0∞)⁻¹ * g (firstSome fun i => att (u i)) =
        ∑ u : Fin κ → α', (Fintype.card (Fin κ → α') : ℝ≥0∞)⁻¹ *
          g (firstSome fun i => att' (u i))
  | 0, g => by
    simp [firstSome]
  | κ + 1, g => by
    rw [avg_fin_succ, avg_fin_succ]
    have hcons : ∀ {γ : Type} (t : γ → Option β) (a : γ) (v : Fin κ → γ),
        (fun i => t ((Fin.cons a v : Fin (κ + 1) → γ) i)) =
          (Fin.cons (t a) (fun i => t (v i)) : Fin (κ + 1) → Option β) := by
      intro γ t a v
      funext i
      refine Fin.cases ?_ ?_ i <;> simp
    simp only [hcons, firstSome_cons]
    have ih := fun o : Option β => avg_firstSome_eq att att' h κ fun o' => g (o.or o')
    simp only [ih]
    exact h fun o => ∑ v : Fin κ → α', (Fintype.card (Fin κ → α') : ℝ≥0∞)⁻¹ *
      g (o.or (firstSome fun i => att' (v i)))

/-- A sum over vectors of length `κ + 1` is the sum over the first entry of the sum over the
    tail. -/
theorem sum_fin_succ_cons {α : Type} [Fintype α] {κ : ℕ} (f : (Fin (κ + 1) → α) → ℝ≥0∞) :
    ∑ v, f v = ∑ a, ∑ v : Fin κ → α, f (Fin.cons a v) := by
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  rfl

/-- Two laws of one coordinate with the same averages give the same averages of every
    function of `N` independent coordinates. -/
theorem avg_fin_pi_eq {α α' γ : Type} [Fintype α] [Fintype α'] (att : α → γ) (att' : α' → γ)
    (h : ∀ g : γ → ℝ≥0∞, ∑ a, (Fintype.card α : ℝ≥0∞)⁻¹ * g (att a) =
      ∑ a, (Fintype.card α' : ℝ≥0∞)⁻¹ * g (att' a)) :
    ∀ (N : ℕ) (g : (Fin N → γ) → ℝ≥0∞),
      ∑ u : Fin N → α, (Fintype.card (Fin N → α) : ℝ≥0∞)⁻¹ * g (fun i => att (u i)) =
        ∑ u : Fin N → α', (Fintype.card (Fin N → α') : ℝ≥0∞)⁻¹ * g (fun i => att' (u i))
  | 0, g => by
    simp [Subsingleton.elim (fun i : Fin 0 => _) (fun i => Fin.elim0 i)]
  | N + 1, g => by
    rw [avg_fin_succ, avg_fin_succ]
    have hcons : ∀ {δ : Type} (t : δ → γ) (a : δ) (v : Fin N → δ),
        (fun i => t ((Fin.cons a v : Fin (N + 1) → δ) i)) =
          (Fin.cons (t a) (fun i => t (v i)) : Fin (N + 1) → γ) := by
      intro δ t a v
      funext i
      refine Fin.cases ?_ ?_ i <;> simp
    simp only [hcons]
    have ih := fun o : γ => avg_fin_pi_eq att att' h N fun t => g (Fin.cons o t)
    simp only [ih]
    exact h fun o => ∑ v : Fin N → α', (Fintype.card (Fin N → α') : ℝ≥0∞)⁻¹ *
      g (Fin.cons o fun i => att' (v i))

/-- Two laws of one coordinate with the same averages give the same averages of every
    function of independent coordinates indexed by a finite type `ι`. -/
theorem avg_pi_eq {ι α α' γ : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype α']
    (att : α → γ) (att' : α' → γ)
    (h : ∀ g : γ → ℝ≥0∞, ∑ a, (Fintype.card α : ℝ≥0∞)⁻¹ * g (att a) =
      ∑ a, (Fintype.card α' : ℝ≥0∞)⁻¹ * g (att' a))
    (g : (ι → γ) → ℝ≥0∞) :
    ∑ u : ι → α, (Fintype.card (ι → α) : ℝ≥0∞)⁻¹ * g (fun i => att (u i)) =
      ∑ u : ι → α', (Fintype.card (ι → α') : ℝ≥0∞)⁻¹ * g (fun i => att' (u i)) := by
  classical
  set e := Fintype.equivFin ι
  have key := avg_fin_pi_eq att att' h (Fintype.card ι) fun t => g fun i => t (e i)
  have hc : ∀ β : Type, [Fintype β] →
      Fintype.card (ι → β) = Fintype.card (Fin (Fintype.card ι) → β) := fun β _ => by
    simp
  rw [hc α, hc α']
  rw [← (e.arrowCongr (Equiv.refl α)).symm.sum_comp,
    ← (e.arrowCongr (Equiv.refl α')).symm.sum_comp]
  simpa [Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Function.comp_def] using key

end FirstSome

/-! ## Reprogramming a uniform table -/

section Reprogram

variable {X Y : Type} [DecidableEq X]

/-- The table `H` overwritten at the points `p i` by the values `c i`, the lowest index
    winning at a point with several indices. -/
def reprog : {N : ℕ} → (Fin N → X) → (Fin N → Y) → (X → Y) → X → Y
  | 0, _, _, H => H
  | _ + 1, p, c, H => Function.update (reprog (Fin.tail p) (Fin.tail c) H) (p 0) (c 0)

variable [Fintype X] [Fintype Y]

/-- Overwriting a table at one point by a value: summed over the table and the value, every
    function of the result has the sum it has on the table. -/
theorem sum_update_eq (x : X) (g : (X → Y) → ℝ≥0∞) :
    ∑ y : Y, ∑ H : X → Y, g (Function.update H x y) = ∑ _y : Y, ∑ H : X → Y, g H := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let e : Equiv.Perm (Y × (X → Y)) :=
    { toFun := fun u => (u.2 x, Function.update u.2 x u.1)
      invFun := fun u => (u.2 x, Function.update u.2 x u.1)
      left_inv := fun u => by simp
      right_inv := fun u => by simp }
  exact Equiv.sum_comp e (fun u : Y × (X → Y) => g u.2)

/-- Replacing the coordinates selected by `s` of a vector by those of an independent vector:
    summed over both vectors, every function of the merged vector has the sum it has on the
    vector. -/
theorem sum_sum_merge_eq {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] (s : ι → Prop)
    [DecidablePred s] (Φ : (ι → β) → ℝ≥0∞) :
    ∑ u₁ : ι → β, ∑ u : ι → β, Φ (fun i => if s i then u₁ i else u i) =
      ∑ _u₁ : ι → β, ∑ u : ι → β, Φ u := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let e : Equiv.Perm ((ι → β) × (ι → β)) :=
    { toFun := fun p => (fun i => if s i then p.2 i else p.1 i,
        fun i => if s i then p.1 i else p.2 i)
      invFun := fun p => (fun i => if s i then p.2 i else p.1 i,
        fun i => if s i then p.1 i else p.2 i)
      left_inv := fun p => Prod.ext (funext fun i => by by_cases h : s i <;> simp [h])
        (funext fun i => by by_cases h : s i <;> simp [h])
      right_inv := fun p => Prod.ext (funext fun i => by by_cases h : s i <;> simp [h])
        (funext fun i => by by_cases h : s i <;> simp [h]) }
  exact Equiv.sum_comp e (fun p : (ι → β) × (ι → β) => Φ p.2)

/-- A weight that does not read a coordinate: if `Φ` does not depend on the coordinate `i₀`
    and, at every table, the sum of `β` over the values at `i₀` is at most `lam · |Y|`, then
    the `Φ`-weighted sum of `β` is at most `lam` times the sum of `Φ`. -/
theorem sum_mul_le_of_update [Nonempty Y] (i₀ : X) (Φ β : (X → Y) → ℝ≥0∞) (lam : ℝ≥0∞)
    (hΦ : ∀ R v, Φ (Function.update R i₀ v) = Φ R)
    (hβ : ∀ R, ∑ v, β (Function.update R i₀ v) ≤ lam * Fintype.card Y) :
    ∑ R, Φ R * β R ≤ lam * ∑ R, Φ R := by
  have key : (Fintype.card Y : ℝ≥0∞) * ∑ R, Φ R * β R =
      ∑ R, Φ R * ∑ v, β (Function.update R i₀ v) := by
    have h := sum_update_eq i₀ fun R => Φ R * β R
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    rw [← h, Finset.sum_comm]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by rw [hΦ]
  have hc0 : (Fintype.card Y : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hct : (Fintype.card Y : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine (ENNReal.mul_le_mul_iff_right hc0 hct).mp ?_
  rw [key]
  calc ∑ R, Φ R * ∑ v, β (Function.update R i₀ v) ≤ ∑ R, Φ R * (lam * Fintype.card Y) :=
        Finset.sum_le_sum fun R _ => by gcongr; exact hβ R
    _ = (Fintype.card Y : ℝ≥0∞) * (lam * ∑ R, Φ R) := by
        rw [← Finset.sum_mul]
        ring

/-- Overwriting a uniform table at points `p` chosen independently of the fresh uniform values
    `c` gives a uniform table: summed over the table and the values, every function of the
    reprogrammed table has the sum it has on the table, for every choice of the points. -/
theorem sum_reprog_eq : ∀ {N : ℕ} (p : Fin N → X) (g : (X → Y) → ℝ≥0∞),
    ∑ c : Fin N → Y, ∑ H : X → Y, g (reprog p c H) = ∑ _c : Fin N → Y, ∑ H : X → Y, g H
  | 0, p, g => by simp [reprog]
  | N + 1, p, g => by
    rw [sum_fin_succ_cons, sum_fin_succ_cons (fun _ => ∑ H : X → Y, g H)]
    simp only [reprog, Fin.tail_cons, Fin.cons_zero]
    have ih := fun y : Y => sum_reprog_eq (Fin.tail p) fun H => g (Function.update H (p 0) y)
    simp only [ih]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun (_ : Y) (_ : Fin N → Y) => ∑ H : X → Y, g H)]
    exact Finset.sum_congr rfl fun _ _ => sum_update_eq (p 0) g

end Reprogram

/-! ## The scheme -/

section Scheme

variable (P : Sigma)

/-- One honest signing attempt at the challenge `e`: the transcript `(a, e, z)` if the
    response is accepted, `none` otherwise. -/
def fsAttempt (x : P.Stmt) (w : P.Wit) (r : P.Rand) (e : P.Ch) :
    Option (P.Com × P.Ch × P.Resp) :=
  if P.accept (P.respond x w r e) then some (P.commit x w r, e, P.respond x w r e) else none

/-- One simulated attempt at the challenge `e`: the simulated transcript if its response is
    accepted, `none` otherwise. -/
def fsSimAttempt (x : P.Stmt) (s : P.SimRand) (e : P.Ch) : Option (P.Com × P.Ch × P.Resp) :=
  if P.accept (P.simulate x e s).2 then some ((P.simulate x e s).1, e, (P.simulate x e s).2)
  else none

/-- Fiat–Shamir with aborts over the Σ-protocol `P` with `κ` attempts: the secret key is the
    statement–witness pair, attempt `i` uses the prover randomness `r i` and reads the
    challenge `H (μ, a_i)` at its commitment `a_i`, and the signature is the challenge and
    response of the first accepted attempt. Verification recovers the commitment with `recom`
    and reads the hash at `(μ, recom x e z)`. -/
def fsAbortSig (κ : ℕ) (Msg : Type) (recom : P.Stmt → P.Ch → P.Resp → P.Com) :
    QROMSig Msg P.Stmt (P.Stmt × P.Wit) (P.Ch × P.Resp) (Msg × P.Com) P.Ch where
  Coins := Fin κ → P.Rand
  keygen := P.gen.map fun xw => (xw.1, xw)
  sign H sk μ r := (firstSome fun i =>
      fsAttempt P sk.1 sk.2 (r i) (H (μ, P.commit sk.1 sk.2 (r i)))).map fun t => (t.2.1, t.2.2)
  point x μ σ := (μ, recom x σ.1 σ.2)
  check x _ σ e := decide (e = σ.1) && P.verify x (recom x σ.1 σ.2) σ.1 σ.2

variable {P}

/-- Verification of `fsAbortSig` reads the hash at the recovered commitment `(μ, recom x e z)`
    and accepts when the value is the challenge `e` and the response is accepted, if the
    verifier of `P` is the acceptance test together with the recovery of the commitment. -/
theorem fsAbortSig_verifyH {κ : ℕ} {Msg : Type} (recom : P.Stmt → P.Ch → P.Resp → P.Com)
    (hrecom : ∀ x a e z, P.verify x a e z = (P.accept z && decide (recom x e z = a)))
    (H : Msg × P.Com → P.Ch) (x : P.Stmt) (μ : Msg) (e : P.Ch) (z : P.Resp) :
    (fsAbortSig P κ Msg recom).verifyH H x μ (e, z) =
      (decide (H (μ, recom x e z) = e) && P.accept z) := by
  simp [QROMSig.verifyH, fsAbortSig, hrecom]

/-! ## Exact simulation of the attempts -/

variable (P)

/-- The view of one transcript: the transcript if its response is accepted, nothing
    otherwise. -/
def attemptView (az : P.Com × P.Resp) : Option (P.Com × P.Resp) :=
  if P.accept az.2 then some az else none

variable {P}

/-- A PMF that is pointwise at most another PMF is equal to it. -/
theorem pmf_eq_of_forall_le {γ : Type} {p p' : PMF γ} (h : ∀ b, p b ≤ p' b) : p = p' := by
  by_contra hne
  obtain ⟨b, hb⟩ : ∃ b, p b ≠ p' b := by
    by_contra hall
    push Not at hall
    exact hne (PMF.ext hall)
  have hlt := ENNReal.tsum_lt_tsum (by simp [PMF.tsum_coe]) h (lt_of_le_of_ne (h b) hb)
  simp [PMF.tsum_coe] at hlt

open Classical in
/-- Under zero HVZK distance at the pair `(x, w)`, the view of the honest attempt and the view
    of the simulated attempt have the same law at every challenge `e`. -/
theorem attemptView_law_eq {x : P.Stmt} {w : P.Wit} (hzk : P.hvzkDistAt x w = 0) (e : P.Ch) :
    (PMF.uniformFintype P.Rand).map (fun r => attemptView P (P.commit x w r, P.respond x w r e)) =
      (PMF.uniformFintype P.SimRand).map fun s => attemptView P (P.simulate x e s) := by
  refine pmf_eq_of_forall_le fun o => ?_
  have hz := P.statHVZKAt_hvzkDistAt x w e (fun az => if attemptView P az = o then 1 else 0)
    (fun _ => by split <;> simp) (fun a a' z hz => by simp [attemptView, hz])
  rw [hzk, add_zero] at hz
  simp only [PMF.map_apply]
  grind

/-- Under zero HVZK distance at the pair `(x, w)`, one honest attempt at a uniform challenge
    and one simulated attempt at a uniform challenge have the same averages. -/
theorem avg_fsAttempt_eq {x : P.Stmt} {w : P.Wit} (hzk : P.hvzkDistAt x w = 0)
    (g : Option (P.Com × P.Ch × P.Resp) → ℝ≥0∞) :
    ∑ u : P.Rand × P.Ch, (Fintype.card (P.Rand × P.Ch) : ℝ≥0∞)⁻¹ * g (fsAttempt P x w u.1 u.2) =
      ∑ u : P.SimRand × P.Ch, (Fintype.card (P.SimRand × P.Ch) : ℝ≥0∞)⁻¹ *
        g (fsSimAttempt P x u.1 u.2) := by
  have key : ∀ e, ∑ r, (Fintype.card P.Rand : ℝ≥0∞)⁻¹ * g (fsAttempt P x w r e) =
      ∑ s, (Fintype.card P.SimRand : ℝ≥0∞)⁻¹ * g (fsSimAttempt P x s e) := by
    intro e
    have h1 : ∀ r, fsAttempt P x w r e =
        (attemptView P (P.commit x w r, P.respond x w r e)).map fun az => (az.1, e, az.2) := by
      intro r
      unfold fsAttempt attemptView
      split <;> rfl
    have h2 : ∀ s, fsSimAttempt P x s e =
        (attemptView P (P.simulate x e s)).map fun az => (az.1, e, az.2) := by
      intro s
      unfold fsSimAttempt attemptView
      split <;> rfl
    have h := congrArg (fun p : PMF (Option (P.Com × P.Resp)) =>
      ∑' o, p o * g (o.map fun az => (az.1, e, az.2))) (attemptView_law_eq hzk e)
    simp only [tsum_map_mul', tsum_fintype, PMF.uniformFintype_apply] at h
    simpa only [h1, h2] using h
  have hc : ∀ (β : Type) [Fintype β],
      (Fintype.card (β × P.Ch) : ℝ≥0∞)⁻¹ =
        (Fintype.card P.Ch : ℝ≥0∞)⁻¹ * (Fintype.card β : ℝ≥0∞)⁻¹ := by
    intro β _
    rw [Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (by simp) (by simp), mul_comm]
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right, hc, hc]
  simp only [mul_assoc, ← Finset.mul_sum, key]

/-- The `κ`-attempt signer at fresh uniform challenges has the law of the `κ`-attempt
    simulator at fresh uniform challenges, under zero HVZK distance at the pair `(x, w)`: the
    averages of every function of the output agree. -/
theorem fsAborts_attempts_sim_eq {x : P.Stmt} {w : P.Wit} (hzk : P.hvzkDistAt x w = 0)
    (κ : ℕ) (g : Option (P.Com × P.Ch × P.Resp) → ℝ≥0∞) :
    ∑ u : Fin κ → P.Rand × P.Ch, (Fintype.card (Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ *
        g (firstSome fun i => fsAttempt P x w (u i).1 (u i).2) =
      ∑ u : Fin κ → P.SimRand × P.Ch, (Fintype.card (Fin κ → P.SimRand × P.Ch) : ℝ≥0∞)⁻¹ *
        g (firstSome fun i => fsSimAttempt P x (u i).1 (u i).2) :=
  avg_firstSome_eq (fun u : P.Rand × P.Ch => fsAttempt P x w u.1 u.2)
    (fun u : P.SimRand × P.Ch => fsSimAttempt P x u.1 u.2) (avg_fsAttempt_eq hzk) κ g

/-- The signers of independent pairs at fresh uniform challenges have the law of the
    simulators of those pairs, under zero HVZK distance at `(x, w)`: the averages of every
    function of the outputs of all pairs agree. -/
theorem fsAborts_pairs_sim_eq {x : P.Stmt} {w : P.Wit} (hzk : P.hvzkDistAt x w = 0)
    (κ : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : (ι → Option (P.Com × P.Ch × P.Resp)) → ℝ≥0∞) :
    ∑ u : ι → Fin κ → P.Rand × P.Ch, (Fintype.card (ι → Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ *
        g (fun y => firstSome fun i => fsAttempt P x w (u y i).1 (u y i).2) =
      ∑ u : ι → Fin κ → P.SimRand × P.Ch,
        (Fintype.card (ι → Fin κ → P.SimRand × P.Ch) : ℝ≥0∞)⁻¹ *
          g (fun y => firstSome fun i => fsSimAttempt P x (u y i).1 (u y i).2) :=
  avg_pi_eq (fun u : Fin κ → P.Rand × P.Ch => firstSome fun i => fsAttempt P x w (u i).1 (u i).2)
    (fun u : Fin κ → P.SimRand × P.Ch => firstSome fun i => fsSimAttempt P x (u i).1 (u i).2)
    (fsAborts_attempts_sim_eq hzk κ) g

/-! ## The commitments of the attempts that are not accepted -/

variable (P)

/-- The commitments of the attempts other than the first accepted one: the rejected attempts
    before it and the attempts after it, which are not executed; all `κ` commitments when every
    attempt is rejected. -/
def nonAccCom (x : P.Stmt) (w : P.Wit) : {κ : ℕ} → (Fin κ → P.Rand × P.Ch) → Finset P.Com
  | 0, _ => ∅
  | _ + 1, u => if (fsAttempt P x w (u 0).1 (u 0).2).isSome then
      Finset.univ.image fun i => P.commit x w (Fin.tail u i).1
    else insert (P.commit x w (u 0).1) (nonAccCom x w (Fin.tail u))

variable {P}

/-- An attempt is rejected exactly when its response is not accepted. -/
theorem fsAttempt_eq_none_iff (x : P.Stmt) (w : P.Wit) (r : P.Rand) (e : P.Ch) :
    fsAttempt P x w r e = none ↔ P.accept (P.respond x w r e) = false := by
  unfold fsAttempt
  split <;> simp_all

/-- Among `κ` uniform attempts, the number with an attempt of commitment `a` is at most
    `κ · commitDistAt` times the number of all. -/
theorem sum_mem_image_commit_le (x : P.Stmt) (w : P.Wit) (a : P.Com) : ∀ κ : ℕ,
    (∑ v : Fin κ → P.Rand × P.Ch,
      if a ∈ Finset.univ.image (fun i => P.commit x w (v i).1) then (1 : ℝ≥0∞) else 0) ≤
      κ * P.commitDistAt x w * ∑ _v : Fin κ → P.Rand × P.Ch, (1 : ℝ≥0∞)
  | 0 => by simp
  | κ + 1 => by
    have ih := sum_mem_image_commit_le x w a κ
    have hpt : ∀ (u0 : P.Rand × P.Ch) (v : Fin κ → P.Rand × P.Ch),
        (if a ∈ Finset.univ.image
            (fun i => P.commit x w ((Fin.cons u0 v : Fin (κ + 1) → P.Rand × P.Ch) i).1)
          then (1 : ℝ≥0∞) else 0) ≤
        (if P.commit x w u0.1 = a then 1 else 0) +
          (if a ∈ Finset.univ.image (fun i => P.commit x w (v i).1) then 1 else 0) := by
      intro u0 v
      split_ifs <;> simp_all [Fin.exists_fin_succ]
    rw [sum_fin_succ_cons, sum_fin_succ_cons (fun _ => (1 : ℝ≥0∞))]
    set N := ∑ _v : Fin κ → P.Rand × P.Ch, (1 : ℝ≥0∞)
    calc _ ≤ ∑ u0 : P.Rand × P.Ch, ∑ v : Fin κ → P.Rand × P.Ch,
          ((if P.commit x w u0.1 = a then 1 else 0) +
            (if a ∈ Finset.univ.image (fun i => P.commit x w (v i).1) then 1 else 0)) :=
          Finset.sum_le_sum fun u0 _ => Finset.sum_le_sum fun v _ => hpt u0 v
      _ = ∑ u0 : P.Rand × P.Ch, ((if P.commit x w u0.1 = a then 1 else 0) * N +
            ∑ v : Fin κ → P.Rand × P.Ch,
              (if a ∈ Finset.univ.image (fun i => P.commit x w (v i).1) then 1 else 0)) := by
          refine Finset.sum_congr rfl fun u0 _ => ?_
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          simp
      _ ≤ ∑ u0 : P.Rand × P.Ch, ((if P.commit x w u0.1 = a then 1 else 0) * N +
            κ * P.commitDistAt x w * N) := by gcongr
      _ = (∑ u0 : P.Rand × P.Ch, if P.commit x w u0.1 = a then (1 : ℝ≥0∞) else 0) * N +
            κ * P.commitDistAt x w * ∑ _u0 : P.Rand × P.Ch, N := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_mul]
      _ ≤ P.commitDistAt x w * (∑ _u0 : P.Rand × P.Ch, (1 : ℝ≥0∞)) * N +
            κ * P.commitDistAt x w * ∑ _u0 : P.Rand × P.Ch, N := by
          gcongr
          exact P.sum_commit_le x w a
      _ = ((κ + 1 : ℕ) : ℝ≥0∞) * P.commitDistAt x w * ∑ _u0 : P.Rand × P.Ch, N := by
          have hN : ∑ _u0 : P.Rand × P.Ch, N = (∑ _u0 : P.Rand × P.Ch, (1 : ℝ≥0∞)) * N := by
            simp
          rw [hN, Nat.cast_succ]
          ring

open Classical in
/-- The rejected commitments given the output: for `κ` uniform attempts and every output
    `o`, the number of attempt vectors with output `o` and an attempt of commitment `a` other
    than the accepted one is at most `κ (ρ ⊔ ε)` times the number with output `o`, where `ρ`
    is `rejCommitDistAt` and `ε` is `commitDistAt`. -/
theorem rejected_mem_cond_le (x : P.Stmt) (w : P.Wit) (o : Option (P.Com × P.Ch × P.Resp))
    (a : P.Com) : ∀ κ : ℕ,
    ∑ u : Fin κ → P.Rand × P.Ch,
        (if (firstSome fun i => fsAttempt P x w (u i).1 (u i).2) = o then (1 : ℝ≥0∞) else 0) *
          (if a ∈ nonAccCom P x w u then 1 else 0) ≤
      κ * (P.rejCommitDistAt x w ⊔ P.commitDistAt x w) *
        ∑ u : Fin κ → P.Rand × P.Ch,
          (if (firstSome fun i => fsAttempt P x w (u i).1 (u i).2) = o then (1 : ℝ≥0∞) else 0)
  | 0 => by simp [nonAccCom]
  | κ + 1 => by
    set lam := P.rejCommitDistAt x w ⊔ P.commitDistAt x w with hlam
    have ih := rejected_mem_cond_le x w o a κ
    set C := ∑ v : Fin κ → P.Rand × P.Ch,
      (if (firstSome fun i => fsAttempt P x w (v i).1 (v i).2) = o then (1 : ℝ≥0∞) else 0)
      with hC
    have hcons : ∀ (u0 : P.Rand × P.Ch) (v : Fin κ → P.Rand × P.Ch),
        (firstSome fun i => fsAttempt P x w ((Fin.cons u0 v : Fin (κ + 1) → P.Rand × P.Ch) i).1
          ((Fin.cons u0 v : Fin (κ + 1) → P.Rand × P.Ch) i).2) =
          (fsAttempt P x w u0.1 u0.2).or
            (firstSome fun i => fsAttempt P x w (v i).1 (v i).2) := by
      intro u0 v
      rw [← firstSome_cons]
      congr 1
      funext i
      refine Fin.cases ?_ ?_ i <;> simp
    have hnon : ∀ (u0 : P.Rand × P.Ch) (v : Fin κ → P.Rand × P.Ch),
        nonAccCom P x w (Fin.cons u0 v : Fin (κ + 1) → P.Rand × P.Ch) =
          if (fsAttempt P x w u0.1 u0.2).isSome then
            Finset.univ.image (fun i => P.commit x w (v i).1)
          else insert (P.commit x w u0.1) (nonAccCom P x w v) := by
      intro u0 v
      simp [nonAccCom]
    set Hs : P.Rand × P.Ch → ℝ≥0∞ := fun u0 => ∑ v : Fin κ → P.Rand × P.Ch,
      (if (fsAttempt P x w u0.1 u0.2).or
          (firstSome fun i => fsAttempt P x w (v i).1 (v i).2) = o then 1 else 0) with hHs
    have hpt : ∀ u0 : P.Rand × P.Ch,
        ∑ v : Fin κ → P.Rand × P.Ch,
          (if (fsAttempt P x w u0.1 u0.2).or
              (firstSome fun i => fsAttempt P x w (v i).1 (v i).2) = o then (1 : ℝ≥0∞) else 0) *
            (if a ∈ (if (fsAttempt P x w u0.1 u0.2).isSome then
                Finset.univ.image (fun i => P.commit x w (v i).1)
              else insert (P.commit x w u0.1) (nonAccCom P x w v)) then 1 else 0) ≤
          (if fsAttempt P x w u0.1 u0.2 = none ∧ P.commit x w u0.1 = a then 1 else 0) * C +
            κ * lam * Hs u0 := by
      intro u0
      simp only [hHs]
      cases h : fsAttempt P x w u0.1 u0.2 with
      | some t =>
        simp only [Option.some_or, Option.isSome_some, ↓reduceIte, reduceCtorEq, false_and,
          zero_mul, zero_add]
        calc ∑ v : Fin κ → P.Rand × P.Ch, (if some t = o then (1 : ℝ≥0∞) else 0) *
              (if a ∈ Finset.univ.image (fun i => P.commit x w (v i).1) then 1 else 0)
            = (if some t = o then (1 : ℝ≥0∞) else 0) * ∑ v : Fin κ → P.Rand × P.Ch,
              (if a ∈ Finset.univ.image (fun i => P.commit x w (v i).1) then 1 else 0) := by
              rw [Finset.mul_sum]
          _ ≤ (if some t = o then (1 : ℝ≥0∞) else 0) *
                (κ * P.commitDistAt x w * ∑ _v : Fin κ → P.Rand × P.Ch, (1 : ℝ≥0∞)) := by
              gcongr
              exact sum_mem_image_commit_le x w a κ
          _ = κ * P.commitDistAt x w * ((if some t = o then (1 : ℝ≥0∞) else 0) *
                ∑ _v : Fin κ → P.Rand × P.Ch, (1 : ℝ≥0∞)) := by ring
          _ ≤ κ * lam * ((if some t = o then (1 : ℝ≥0∞) else 0) *
                ∑ _v : Fin κ → P.Rand × P.Ch, (1 : ℝ≥0∞)) := by gcongr; exact le_sup_right
          _ = κ * lam * ∑ _v : Fin κ → P.Rand × P.Ch, (if some t = o then (1 : ℝ≥0∞) else 0) := by
              rw [Finset.mul_sum]
              simp
      | none =>
        simp only [Option.none_or, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          true_and]
        calc ∑ v : Fin κ → P.Rand × P.Ch,
              (if (firstSome fun i => fsAttempt P x w (v i).1 (v i).2) = o then (1 : ℝ≥0∞)
                else 0) *
              (if a ∈ insert (P.commit x w u0.1) (nonAccCom P x w v) then 1 else 0)
            ≤ ∑ v : Fin κ → P.Rand × P.Ch, ((if P.commit x w u0.1 = a then 1 else 0) *
                (if (firstSome fun i => fsAttempt P x w (v i).1 (v i).2) = o then (1 : ℝ≥0∞)
                  else 0) +
                (if (firstSome fun i => fsAttempt P x w (v i).1 (v i).2) = o then (1 : ℝ≥0∞)
                  else 0) * (if a ∈ nonAccCom P x w v then 1 else 0)) := by
              refine Finset.sum_le_sum fun v _ => ?_
              split_ifs <;> simp_all
          _ ≤ (if P.commit x w u0.1 = a then 1 else 0) * C + κ * lam * C := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
              gcongr
    rw [sum_fin_succ_cons, sum_fin_succ_cons]
    simp only [hcons, hnon]
    have hrej : (∑ u0 : P.Rand × P.Ch,
        if fsAttempt P x w u0.1 u0.2 = none ∧ P.commit x w u0.1 = a then (1 : ℝ≥0∞) else 0) ≤
        lam * ∑ u0 : P.Rand × P.Ch,
          if fsAttempt P x w u0.1 u0.2 = none then (1 : ℝ≥0∞) else 0 := by
      simp only [fsAttempt_eq_none_iff]
      exact (P.sum_rej_commit_le x w a).trans (by gcongr; exact le_sup_left)
    have hrejC : (∑ u0 : P.Rand × P.Ch,
        if fsAttempt P x w u0.1 u0.2 = none then (1 : ℝ≥0∞) else 0) * C ≤ ∑ u0, Hs u0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun u0 _ => ?_
      split_ifs with h
      · simp [hHs, h, hC]
      · simp
    calc _ ≤ ∑ u0 : P.Rand × P.Ch,
          ((if fsAttempt P x w u0.1 u0.2 = none ∧ P.commit x w u0.1 = a then 1 else 0) * C +
            κ * lam * Hs u0) := Finset.sum_le_sum fun u0 _ => hpt u0
      _ = (∑ u0 : P.Rand × P.Ch,
            if fsAttempt P x w u0.1 u0.2 = none ∧ P.commit x w u0.1 = a then (1 : ℝ≥0∞)
              else 0) * C + κ * lam * ∑ u0, Hs u0 := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      _ ≤ lam * ((∑ u0 : P.Rand × P.Ch,
            if fsAttempt P x w u0.1 u0.2 = none then (1 : ℝ≥0∞) else 0) * C) +
            κ * lam * ∑ u0, Hs u0 := by
          rw [← mul_assoc]
          gcongr
      _ ≤ lam * ∑ u0, Hs u0 + κ * lam * ∑ u0, Hs u0 := by gcongr
      _ = ((κ + 1 : ℕ) : ℝ≥0∞) * lam * ∑ u0, Hs u0 := by
          rw [Nat.cast_succ]
          ring

end Scheme

/-! ## Programming a table at rows of entries -/

section Program

variable {X Y : Type} [DecidableEq X]

/-- The value of an optional point–value entry at the point `x`: `some v` if the entry is
    `(x, v)`, `none` otherwise. -/
def matchAt (x : X) (o : Option (X × Y)) : Option Y :=
  o.bind fun p => if p.1 = x then some p.2 else none

/-- The table `H` programmed at the entries `d j`, the first entry at a point winning. -/
def prog1 {N : ℕ} (d : Fin N → Option (X × Y)) (H : X → Y) (x : X) : Y :=
  (firstSome fun j => matchAt x (d j)).getD (H x)

/-- The table `H` programmed at the rows of entries `d j`, the rows in order and the entries
    of a row in order, the first entry at a point winning. -/
def prog2 {N κ : ℕ} (d : Fin N → Fin κ → Option (X × Y)) (H : X → Y) (x : X) : Y :=
  (firstSome fun j => firstSome fun i => matchAt x (d j i)).getD (H x)

/-- `getD` of the first defined of two options. -/
theorem getD_or (o o' : Option Y) (y : Y) : (o.or o').getD y = o.getD (o'.getD y) := by
  cases o <;> rfl

/-- `firstSome` of a vector of `none` entries is `none`. -/
theorem firstSome_eq_none {β : Type} : ∀ {κ : ℕ} (v : Fin κ → Option β), (∀ i, v i = none) →
    firstSome v = none
  | 0, _, _ => rfl
  | _ + 1, v, h => by
    simp only [firstSome, h 0, Option.none_or]
    exact firstSome_eq_none _ fun i => h i.succ

/-- `firstSome` of a vector whose entries other than `i` are `none` is the entry `i`. -/
theorem firstSome_eq_of_forall_ne {β : Type} : ∀ {κ : ℕ} (v : Fin κ → Option β) (i : Fin κ),
    (∀ i', i' ≠ i → v i' = none) → firstSome v = v i
  | 0, _, i, _ => i.elim0
  | _ + 1, v, i, h => by
    induction i using Fin.cases with
    | zero =>
      have ht : firstSome (Fin.tail v) = none :=
        firstSome_eq_none _ fun i' => h i'.succ (Fin.succ_ne_zero i')
      simp [firstSome, ht]
    | succ i =>
      have h0 : v 0 = none := h 0 (Fin.succ_ne_zero i).symm
      have ih := firstSome_eq_of_forall_ne (Fin.tail v) i fun i' hi' =>
        h i'.succ fun he => hi' (Fin.succ_injective _ he)
      simp only [firstSome, h0, Option.none_or, ih]
      rfl

/-- The table programmed at rows of entries, at a point `z` matched by the entry `(j, i)`
    only, has the value of that entry. -/
theorem prog2_eq_of_unique {N κ : ℕ} (d : Fin N → Fin κ → Option (X × Y)) (H : X → Y) (z : X)
    (j : Fin N) (i : Fin κ) (v : Y) (hd : d j i = some (z, v))
    (hu : ∀ j' i', (j', i') ≠ (j, i) → matchAt z (d j' i') = none) : prog2 d H z = v := by
  unfold prog2
  rw [firstSome_eq_of_forall_ne _ j fun j' hj' =>
    firstSome_eq_none _ fun i' => hu j' i' (by simp [hj'])]
  rw [firstSome_eq_of_forall_ne _ i fun i' hi' => hu j i' (by simp [hi'])]
  simp [matchAt, hd]

/-- `reprog` is the table programmed at the entries `(p i, c i)`, the first winning. -/
theorem reprog_apply_eq : ∀ {N : ℕ} (p : Fin N → X) (c : Fin N → Y) (H : X → Y) (x : X),
    reprog p c H x = (firstSome fun i => matchAt x (some (p i, c i))).getD (H x)
  | 0, _, _, _, _ => rfl
  | N + 1, p, c, H, x => by
    rw [reprog, Function.update_apply, reprog_apply_eq]
    by_cases h : x = p 0
    · simp [firstSome, matchAt, h]
    · simp [firstSome, matchAt, h, Ne.symm h, Fin.tail]
      rfl

/-- Programming the rows `0, …, N` is programming row `0` over the programming of the rows
    after it. -/
theorem prog2_succ {N κ : ℕ} (p : Fin (N + 1) → Fin κ → X) (c : Fin (N + 1) → Fin κ → Y)
    (H : X → Y) :
    prog2 (fun j i => some (p j i, c j i)) H =
      reprog (p 0) (c 0) (prog2 (fun j i => some (p j.succ i, c j.succ i)) H) := by
  funext x
  rw [reprog_apply_eq]
  unfold prog2
  simp only [firstSome]
  rw [getD_or]
  rfl

/-- A defined `firstSome` is an entry of the vector. -/
theorem exists_of_firstSome_eq_some {β : Type} : ∀ {κ : ℕ} (v : Fin κ → Option β) (b : β),
    firstSome v = some b → ∃ i, v i = some b
  | 0, _, _, h => by simp [firstSome] at h
  | _ + 1, v, b, h => by
    simp only [firstSome] at h
    cases h0 : v 0 with
    | none =>
      rw [h0, Option.none_or] at h
      obtain ⟨i, hi⟩ := exists_of_firstSome_eq_some _ b h
      exact ⟨i.succ, hi⟩
    | some b' =>
      rw [h0, Option.some_or] at h
      exact ⟨0, h0.trans h⟩

/-- The table programmed at the rows of `d` is the table programmed at row `0` over the table
    programmed at the rows after it. -/
theorem prog2_succ_apply {N κ : ℕ} (d : Fin (N + 1) → Fin κ → Option (X × Y)) (H : X → Y)
    (x : X) :
    prog2 d H x =
      (firstSome fun i => matchAt x (d 0 i)).getD (prog2 (fun j => d j.succ) H x) := by
  unfold prog2
  simp only [firstSome]
  rw [getD_or]
  rfl

/-- The rows of `d` split by `s` into two families whose entries never share a point: the
    table programmed at all rows is the table programmed at the rows outside `s` over the
    table programmed at the rows in `s`. -/
theorem prog2_split {N κ : ℕ} (d : Fin N → Fin κ → Option (X × Y)) (s : Fin N → Prop)
    [DecidablePred s] (H : X → Y)
    (hdisj : ∀ x, (∀ j i, s j → matchAt x (d j i) = none) ∨
      (∀ j i, ¬ s j → matchAt x (d j i) = none)) :
    prog2 d H = prog2 (fun j i => if s j then none else d j i)
      (prog2 (fun j i => if s j then d j i else none) H) := by
  funext x
  unfold prog2
  rcases hdisj x with h | h
  · have e1 : (fun j => firstSome fun i => matchAt x (d j i)) =
        fun j => firstSome fun i => matchAt x (if s j then none else d j i) := by
      funext j
      congr 1
      funext i
      by_cases hs : s j
      · rw [h j i hs]
        simp [hs, matchAt]
      · simp [hs]
    have e2 : (firstSome fun j => firstSome fun i =>
        matchAt x (if s j then d j i else none)) = none :=
      firstSome_eq_none _ fun j => firstSome_eq_none _ fun i => by
        by_cases hs : s j
        · simp [hs, h j i hs]
        · simp [hs, matchAt]
    rw [e1, e2]
    rfl
  · have e1 : (fun j => firstSome fun i => matchAt x (d j i)) =
        fun j => firstSome fun i => matchAt x (if s j then d j i else none) := by
      funext j
      congr 1
      funext i
      by_cases hs : s j
      · simp [hs]
      · rw [h j i hs]
        simp [hs, matchAt]
    have e2 : (firstSome fun j => firstSome fun i =>
        matchAt x (if s j then none else d j i)) = none :=
      firstSome_eq_none _ fun j => firstSome_eq_none _ fun i => by
        by_cases hs : s j
        · simp [hs, matchAt]
        · simp [hs, h j i hs]
    rw [e1, e2]
    rfl

variable [Fintype X] [Fintype Y]

/-- Overwriting a uniform table at rows of points by fresh uniform values gives a uniform
    table: summed over the table and the values, every function of the programmed table has
    the sum it has on the table, for every choice of the points. -/
theorem sum_prog2_eq {κ : ℕ} : ∀ {N : ℕ} (p : Fin N → Fin κ → X) (g : (X → Y) → ℝ≥0∞),
    ∑ c : Fin N → Fin κ → Y, ∑ H : X → Y, g (prog2 (fun j i => some (p j i, c j i)) H) =
      ∑ _c : Fin N → Fin κ → Y, ∑ H : X → Y, g H
  | 0, _, _ => rfl
  | N + 1, p, g => by
    rw [sum_fin_succ_cons, sum_fin_succ_cons (fun _ => ∑ H : X → Y, g H)]
    simp only [prog2_succ, Fin.cons_zero, Fin.cons_succ]
    have ih := fun y : Fin κ → Y =>
      sum_prog2_eq (fun j : Fin N => p j.succ) fun H => g (reprog (p 0) y H)
    simp only [ih]
    rw [Finset.sum_comm, Finset.sum_comm
      (f := fun (_ : Fin κ → Y) (_ : Fin N → Fin κ → Y) => ∑ H : X → Y, g H)]
    exact Finset.sum_congr rfl fun _ _ => sum_reprog_eq (p 0) g

/-- Overwriting a uniform table at the rows selected by `s` by fresh uniform values gives a
    uniform table, for every choice of the points. -/
theorem sum_prog2_sel_eq {κ : ℕ} : ∀ {N : ℕ} (s : Fin N → Prop) [DecidablePred s]
    (p : Fin N → Fin κ → X) (g : (X → Y) → ℝ≥0∞),
    ∑ c : Fin N → Fin κ → Y, ∑ H : X → Y,
        g (prog2 (fun j i => if s j then some (p j i, c j i) else none) H) =
      ∑ _c : Fin N → Fin κ → Y, ∑ H : X → Y, g H
  | 0, _, _, _, _ => rfl
  | N + 1, s, _, p, g => by
    rw [sum_fin_succ_cons, sum_fin_succ_cons (fun _ => ∑ H : X → Y, g H)]
    by_cases hs : s 0
    · have hp : ∀ (y : Fin κ → Y) (c : Fin N → Fin κ → Y) (H : X → Y),
          prog2 (fun j i => if s j then
            some (p j i, (Fin.cons y c : Fin (N + 1) → Fin κ → Y) j i) else none) H =
          reprog (p 0) y (prog2 (fun j i => if s j.succ then some (p j.succ i, c j i)
            else none) H) := by
        intro y c H
        funext x
        rw [prog2_succ_apply, reprog_apply_eq]
        simp only [hs, ite_true, Fin.cons_zero, Fin.cons_succ]
      simp only [hp]
      have ih := fun y : Fin κ → Y => sum_prog2_sel_eq (fun j : Fin N => s j.succ)
        (fun j : Fin N => p j.succ) fun H => g (reprog (p 0) y H)
      simp only [ih]
      rw [Finset.sum_comm, Finset.sum_comm
        (f := fun (_ : Fin κ → Y) (_ : Fin N → Fin κ → Y) => ∑ H : X → Y, g H)]
      exact Finset.sum_congr rfl fun _ _ => sum_reprog_eq (p 0) g
    · have hp : ∀ (y : Fin κ → Y) (c : Fin N → Fin κ → Y) (H : X → Y),
          prog2 (fun j i => if s j then
            some (p j i, (Fin.cons y c : Fin (N + 1) → Fin κ → Y) j i) else none) H =
          prog2 (fun j i => if s j.succ then some (p j.succ i, c j i) else none) H := by
        intro y c H
        funext x
        rw [prog2_succ_apply, firstSome_eq_none _ fun i => by simp [hs, matchAt]]
        simp only [Fin.cons_succ]
        rfl
      simp only [hp]
      have ih := sum_prog2_sel_eq (fun j : Fin N => s j.succ) (fun j : Fin N => p j.succ) g
      simp only [ih]

end Program

/-! ## Diagonal final tests -/

section FinalTests

variable {m n w q : ℕ} [NeZero n]

open Matrix CatCrypt.Quantum in
/-- The acceptance probability of a run is at most one. -/
theorem prOut_le_one (B : QAdv m n w q) (H : Fin m → Fin n) : prOut B H ≤ 1 := by
  unfold prOut prTrue_Q
  have h : ((run B H).branch true B.init.val).trace.re ≤ B.init.val.trace.re :=
    calc ((run B H).branch true B.init.val).trace.re
        ≤ ∑' b, ((run B H).branch b B.init.val).trace.re :=
          (trace_re_summable ((run B H).branch_summable _)).le_tsum true
            (fun b _ => trace_re_nonneg_of_psd ((run B H).branch_psd b _ B.init.psd))
      _ = (∑' b, ((run B H).branch b B.init.val).trace).re :=
          (Complex.re_tsum (trace_summable ((run B H).branch_summable _))).symm
      _ ≤ B.init.val.trace.re := (run B H).branch_stp _ B.init.psd
  rw [B.init.tr_one, Complex.one_re] at h
  exact ENNReal.ofReal_le_one.mpr h

/-- The diagonal test that rejects every basis state accepts with probability zero. -/
theorem prOut_withFinalB_false (B : QAdv m n w q) (H : Fin m → Fin n) :
    prOut (B.withFinalB fun _ => false) H = 0 := by
  rw [prOut_withFinalB_eq_prOutW]
  simp [prOutW, diagW]

/-- The acceptance probability of a diagonal test `G` is the sum, over the values `z` of a
    function `φ` of the basis states, of the acceptance probabilities of `G ∧ φ = z`. -/
theorem prOut_withFinalB_eq_sum {Z : Type} [Fintype Z] [DecidableEq Z] (B : QAdv m n w q)
    (G : Fin (m * n * w) → Bool) (φ : Fin (m * n * w) → Z) (H : Fin m → Fin n) :
    prOut (B.withFinalB G) H =
      ∑ z, prOut (B.withFinalB fun i => G i && decide (φ i = z)) H := by
  simp only [prOut_withFinalB_eq_prOutW]
  rw [← ENNReal.ofReal_sum_of_nonneg fun z _ =>
    prOutW_nonneg B (fun i => by dsimp only; split_ifs <;> simp) H]
  congr 1
  have h := prOutW_sum B Finset.univ (fun _ => (1 : ℝ))
    (fun z i => if (G i && decide (φ i = z)) then 1 else 0) H
  simp only [one_mul, one_smul] at h
  rw [← h]
  congr 1
  funext i
  rw [Finset.sum_apply]
  cases G i <;> simp

end FinalTests

/-! ## Routing the queries of an adversary to simulate a programmed oracle -/

section Route

open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct

variable {m n w c : ℕ} {Γ : Type}

/-- The index of `(((x, y), z), a)` on the register with the ancilla `Γ ≃ Fin c` inside the work
    register: the oracle index of `((x, y), (z, eC a))`. -/
def ancRegIdx (eC : Γ ≃ Fin c) : ((Fin m × Fin n) × Fin w) × Γ ≃ Fin (m * n * (w * c)) :=
  (Equiv.prodAssoc _ _ _).trans <|
    ((Equiv.refl _).prodCongr ((Equiv.refl (Fin w)).prodCongr eC)).trans <|
      ((Equiv.refl _).prodCongr (finProdEquiv w c)).trans (oracleIndex m n (w * c))

/-- The index `ancRegIdx` read through `ancE` is the pair of the oracle index of the register
    and the ancilla index. -/
theorem ancE_symm_ancRegIdx (eC : Γ ≃ Fin c) (t : (Fin m × Fin n) × Fin w) (a : Γ) :
    (ancE m n w c).symm (ancRegIdx eC (t, a)) =
      finProdEquiv (m * n * w) c (oracleIndex m n w t, eC a) := by
  apply Fin.ext
  simp only [ancRegIdx, ancE, oracleIndex, finProdEquiv, finCongr_symm, finCongr_apply,
    Fin.val_cast, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
    id_eq, finProdFinEquiv_apply_val, Equiv.prodAssoc_apply]
  ring

/-- The entries of `kr` at the indices `ancRegIdx` are products of entries. -/
theorem kr_ancRegIdx_apply (eC : Γ ≃ Fin c) (A : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ)
    (B : Matrix (Fin c) (Fin c) ℂ) (t t' : (Fin m × Fin n) × Fin w) (a a' : Γ) :
    kr (ancE m n w c) A B (ancRegIdx eC (t, a)) (ancRegIdx eC (t', a')) =
      A (oracleIndex m n w t) (oracleIndex m n w t') * B (eC a) (eC a') := by
  simp only [kr, Matrix.submatrix_apply, ancE_symm_ancRegIdx, kronecker_apply,
    Equiv.symm_apply_apply]

variable [NeZero n]

/-- The oracle on the extended register acts on the indices `ancRegIdx` as on the query
    register. -/
theorem oraclePerm_ancRegIdx (eC : Γ ≃ Fin c) (H : Fin m → Fin n) (x : Fin m) (y : Fin n)
    (z : Fin w) (a : Γ) :
    oraclePerm m n (w * c) H (ancRegIdx eC (((x, y), z), a)) =
      ancRegIdx eC (((x, y + H x), z), a) := by
  simp only [ancRegIdx, Equiv.trans_apply, Equiv.prodAssoc_apply, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map, id_eq, oraclePerm_apply]

end Route

section PermRow

open Matrix CatCrypt.Quantum

variable {d : ℕ}

/-- Row `σ k` of `permUnitary σ * X` is row `k` of `X`. -/
theorem permUnitary_mul_apply_self (σ : Equiv.Perm (Fin d)) (X : Matrix (Fin d) (Fin d) ℂ)
    (k j : Fin d) : ((permUnitary σ : Matrix (Fin d) (Fin d) ℂ) * X) (σ k) j = X k j := by
  simp [Matrix.mul_apply]

/-- `permUnitary σ` times its conjugate transpose is the identity. -/
theorem permUnitary_mul_conjTranspose (σ : Equiv.Perm (Fin d)) :
    (permUnitary σ : Matrix (Fin d) (Fin d) ℂ) * (permUnitary σ : Matrix (Fin d) (Fin d) ℂ)ᴴ =
      1 :=
  Matrix.mem_unitaryGroup_iff.mp (permUnitary σ).prop

/-- The chain operator of the unitaries `A U_i B` is `A` times the chain operator of `U` with
    the oracle `B O A`, times `B`. -/
theorem chainOp_sandwich (O A B : Matrix (Fin d) (Fin d) ℂ) :
    ∀ (q : ℕ) (U V : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      (∀ i, (V i : Matrix (Fin d) (Fin d) ℂ) = A * U i * B) →
        chainOp O q V = A * chainOp (B * O * A) q U * B
  | 0, _, _, h => h 0
  | q + 1, U, V, h => by
    have ih := chainOp_sandwich O A B q (Fin.tail U) (Fin.tail V) fun i => h i.succ
    simp only [chainOp, ih, h 0, Matrix.mul_assoc]

end PermRow

section RouteAdv

open scoped ComplexOrder

open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct

variable {m n w q : ℕ}

/-- The coordinates of the register with the router ancilla: the query register, the work
    register, a flag and a saved query register. -/
abbrev RouteCoord (m n w : ℕ) := ((Fin m × Fin n) × Fin w) × (Bool × (Fin m × Fin n))

/-- The router at the points `G`: with the flag down and the query point in `G`, the query
    register is swapped with the saved register and the flag raised; with the flag up and the
    saved point in `G`, the swap is undone; every other basis state is fixed. -/
def routeFun (G : Fin m → Bool) (u : RouteCoord m n w) : RouteCoord m n w :=
  if (if u.2.1 then G u.2.2.1 else G u.1.1.1) then ((u.2.2, u.1.2), (!u.2.1, u.1.1)) else u

/-- The router is an involution. -/
theorem routeFun_involutive (G : Fin m → Bool) :
    Function.Involutive (routeFun (n := n) (w := w) G) := by
  rintro ⟨⟨⟨x, y⟩, z⟩, b, a⟩
  cases b <;> cases hx : G x <;> cases ha : G a.1 <;> simp [routeFun, hx, ha]

/-- The index of the router ancilla: the flag and the saved query register. -/
def routeAncE (m n : ℕ) : Bool × (Fin m × Fin n) ≃ Fin (2 * (m * n)) :=
  (finTwoEquiv.symm.prodCongr (finProdEquiv m n)).trans (finProdEquiv 2 (m * n))

/-- The router as a permutation of the register with the router ancilla. -/
def routePerm (G : Fin m → Bool) : Equiv.Perm (Fin (m * n * (w * (2 * (m * n))))) :=
  (ancRegIdx (routeAncE m n)).permCongr (Function.Involutive.toPerm _ (routeFun_involutive G))

/-- `routePerm G` acts on the indices `ancRegIdx` as `routeFun G`. -/
theorem routePerm_ancRegIdx (G : Fin m → Bool) (u : RouteCoord m n w) :
    routePerm G (ancRegIdx (routeAncE m n) u) = ancRegIdx (routeAncE m n) (routeFun G u) := by
  simp [routePerm, Equiv.permCongr_apply]

/-- The oracle `H` programmed by the partial table `p`: `p x` where it is defined, `H x`
    elsewhere. -/
def progOracle (p : Fin m → Option (Fin n)) (H : Fin m → Fin n) : Fin m → Fin n :=
  fun x => (p x).getD (H x)

variable [NeZero n]

/-- The routed query at the partial table `p`: the router, the query to `H`, the router, then
    the programmed values added to the value register. -/
def routeQuery (p : Fin m → Option (Fin n)) (H : Fin m → Fin n) :
    Equiv.Perm (Fin (m * n * (w * (2 * (m * n))))) :=
  oraclePerm m n _ (fun x => (p x).getD 0) * routePerm (fun x => (p x).isSome) *
    oraclePerm m n _ H * routePerm (fun x => (p x).isSome)

/-- The routed query keeps the flag and the saved point, and with the flag down it is the
    query to the programmed oracle. -/
theorem routeQuery_ancRegIdx (p : Fin m → Option (Fin n)) (H : Fin m → Fin n)
    (t : (Fin m × Fin n) × Fin w) (b : Bool) (a : Fin m × Fin n) :
    ∃ t' a₂, routeQuery p H (ancRegIdx (routeAncE m n) (t, (b, a))) =
        ancRegIdx (routeAncE m n) (t', (b, (a.1, a₂))) ∧
      (b = false → t' = ((t.1.1, t.1.2 + progOracle p H t.1.1), t.2)) := by
  obtain ⟨⟨x, y⟩, z⟩ := t
  obtain ⟨a₁, a₂⟩ := a
  cases b <;> cases hx : p x <;> cases ha : p a₁ <;>
    simp [routeQuery, routePerm_ancRegIdx, routeFun, oraclePerm_ancRegIdx, progOracle, hx, ha]

variable [NeZero m]

/-- The state of the router ancilla: the flag down and the saved register `|0⟩ ⊗ |+⟩`, the
    uniform superposition of the values at the point `0`, which every query leaves fixed. -/
def routeAncState (m n : ℕ) [NeZero m] : Matrix (Fin (2 * (m * n))) (Fin (2 * (m * n))) ℂ :=
  Matrix.of fun k l =>
    if ((routeAncE m n).symm k).1 = false ∧ ((routeAncE m n).symm k).2.1 = 0 ∧
        ((routeAncE m n).symm l).1 = false ∧ ((routeAncE m n).symm l).2.1 = 0 then (n : ℂ)⁻¹
    else 0

omit [NeZero n] in
/-- The entries of `routeAncState` at the router coordinates. -/
theorem routeAncState_apply (b b' : Bool) (a a' : Fin m × Fin n) :
    routeAncState m n (routeAncE m n (b, a)) (routeAncE m n (b', a')) =
      if b = false ∧ a.1 = 0 ∧ b' = false ∧ a'.1 = 0 then (n : ℂ)⁻¹ else 0 := by
  simp [routeAncState]

omit [NeZero n] in
/-- `routeAncState` is self-adjoint. -/
theorem routeAncState_conjTranspose : (routeAncState m n)ᴴ = routeAncState m n := by
  ext k l
  simp only [routeAncState, conjTranspose_apply, of_apply]
  split_ifs <;> simp_all

omit [NeZero n] in
/-- `routeAncState` is positive semidefinite. -/
theorem routeAncState_posSemidef : (routeAncState m n).PosSemidef := by
  set χ : Fin (2 * (m * n)) → ℂ := fun k =>
    if ((routeAncE m n).symm k).1 = false ∧ ((routeAncE m n).symm k).2.1 = 0 then 1 else 0
    with hχ
  have h : routeAncState m n = (n : ℂ)⁻¹ • vecMulVec χ (star χ) := by
    ext k l
    simp only [routeAncState, of_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, hχ]
    split_ifs <;> simp_all
  rw [h]
  exact (posSemidef_vecMulVec_self_star χ).smul (by simp)

/-- `routeAncState` has trace one. -/
theorem trace_routeAncState : (routeAncState m n).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [← (routeAncE m n).sum_comp]
  simp [routeAncState_apply, Fintype.sum_prod_type]

/-- The routed query on a state with the router ancilla in `routeAncState` is the query to the
    programmed oracle. -/
theorem routeQuery_mul_kr (p : Fin m → Option (Fin n)) (H : Fin m → Fin n)
    (M : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (permUnitary (routeQuery (w := w) p H) : Matrix _ _ ℂ) *
        kr (ancE m n w (2 * (m * n))) M (routeAncState m n) =
      kr (ancE m n w (2 * (m * n)))
        ((permUnitary (oraclePerm m n w (progOracle p H)) : Matrix _ _ ℂ) * M)
        (routeAncState m n) := by
  ext i j
  obtain ⟨⟨t, b, a⟩, rfl⟩ : ∃ v, routeQuery p H (ancRegIdx (routeAncE m n) v) = i :=
    ⟨(ancRegIdx (routeAncE m n)).symm ((routeQuery p H).symm i), by simp⟩
  obtain ⟨⟨t', b', a'⟩, rfl⟩ : ∃ v, ancRegIdx (routeAncE m n) v = j :=
    ⟨(ancRegIdx (routeAncE m n)).symm j, by simp⟩
  obtain ⟨t₁, a₂, h, ht⟩ := routeQuery_ancRegIdx p H t b a
  rw [permUnitary_mul_apply_self, h, kr_ancRegIdx_apply, kr_ancRegIdx_apply,
    routeAncState_apply, routeAncState_apply]
  cases b
  · obtain ⟨⟨x, y⟩, z⟩ := t
    rw [ht rfl, show oracleIndex m n w ((x, y + progOracle p H x), z) =
      oraclePerm m n w (progOracle p H) (oracleIndex m n w ((x, y), z)) by simp,
      permUnitary_mul_apply_self]
  · simp

/-- The chain of routed queries on a state with the router ancilla in `routeAncState` is the
    chain of queries to the programmed oracle. -/
theorem chainOp_routeQuery_kr (p : Fin m → Option (Fin n)) (H : Fin m → Fin n) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ)
      (X : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ),
      chainOp (permUnitary (routeQuery (w := w) p H) : Matrix _ _ ℂ) q
          (liftU (ancE m n w (2 * (m * n))) ∘ U) *
          kr (ancE m n w (2 * (m * n))) X (routeAncState m n) =
        kr (ancE m n w (2 * (m * n)))
          (chainOp (oracleU m n w (progOracle p H) : Matrix _ _ ℂ) q U * X) (routeAncState m n)
  | 0, U, X => by
    simp only [chainOp, Function.comp_apply, liftU_val, kr_mul, one_mul]
  | q + 1, U, X => by
    have ih := chainOp_routeQuery_kr p H q (Fin.tail U)
    simp only [chainOp]
    rw [show Fin.tail (liftU (ancE m n w (2 * (m * n))) ∘ U) =
      liftU (ancE m n w (2 * (m * n))) ∘ Fin.tail U from rfl]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Function.comp_apply, liftU_val, kr_mul, one_mul,
      routeQuery_mul_kr, ih, oracleU_eq_permUnitary]
    simp only [Matrix.mul_assoc]

/-- The permutation before each query of the routed adversary: the router, then the programmed
    values added (`routeQuery` is `routeIn`, the query, the router). -/
def routeIn (p : Fin m → Option (Fin n)) : Equiv.Perm (Fin (m * n * (w * (2 * (m * n))))) :=
  oraclePerm m n _ (fun x => (p x).getD 0) * routePerm (fun x => (p x).isSome)

/-- The adversary `F` against the oracle `progOracle p H`, run with plain access to `H`: the
    router ancilla starts in `routeAncState`, each query is routed (`routeQuery`), and the
    final projector is that of `F`. A query at a programmed point is swapped into the saved
    register, the query to `H` acts on `|0⟩ ⊗ |+⟩`, which it leaves fixed, and the programmed
    value is added. -/
def routeAdv (F : QAdv m n w q) (p : Fin m → Option (Fin n)) :
    QAdv m n (w * (2 * (m * n))) q where
  U i := permUnitary (routePerm (n := n) (w := w) (fun x => (p x).isSome)) *
    liftU (ancE m n w (2 * (m * n))) (F.U i) * permUnitary (routeIn p)
  init :=
    { val := (permUnitary (routeIn (w := w) p) : Matrix _ _ ℂ)ᴴ *
        kr (ancE m n w (2 * (m * n))) F.init.val (routeAncState m n) *
        (permUnitary (routeIn (w := w) p) : Matrix _ _ ℂ)
      psd := (kr_posSemidef _ F.init.psd routeAncState_posSemidef).conjTranspose_mul_mul_same _
      tr_one := by
        rw [Matrix.trace_mul_cycle, permUnitary_mul_conjTranspose, Matrix.one_mul, trace_kr,
          F.init.tr_one, trace_routeAncState, one_mul] }
  final := (permUnitary (routePerm (n := n) (w := w) (fun x => (p x).isSome)) : Matrix _ _ ℂ) *
    kr (ancE m n w (2 * (m * n))) F.final 1 *
    (permUnitary (routePerm (n := n) (w := w) (fun x => (p x).isSome)) : Matrix _ _ ℂ)ᴴ
  final_conjTranspose := by
    rw [permUnitary_conj, conjTranspose_submatrix, kr_conjTranspose, F.final_conjTranspose,
      conjTranspose_one]
  final_mul_self := by
    rw [permUnitary_conj, Matrix.submatrix_mul_equiv, kr_mul, F.final_mul_self, one_mul]

/-- The routed adversary against `H` accepts with the probability of `F` against the
    programmed oracle `progOracle p H`. -/
theorem prOut_routeAdv (F : QAdv m n w q) (p : Fin m → Option (Fin n)) (H : Fin m → Fin n) :
    prOut (routeAdv F p) H = prOut F (progOracle p H) := by
  set PR : Matrix (Fin (m * n * (w * (2 * (m * n))))) (Fin (m * n * (w * (2 * (m * n))))) ℂ :=
    (permUnitary (routePerm (n := n) (w := w) (fun x => (p x).isSome))).1 with hPR
  set PB : Matrix (Fin (m * n * (w * (2 * (m * n))))) (Fin (m * n * (w * (2 * (m * n))))) ℂ :=
    (permUnitary (routeIn (w := w) p)).1 with hPB
  set e := ancE m n w (2 * (m * n)) with he
  set C := chainOp (permUnitary (routeQuery (w := w) p H) : Matrix _ _ ℂ) q (liftU e ∘ F.U)
    with hCdef
  set R' := runOp F (progOracle p H) with hR'
  have hrun : runOp (routeAdv F p) H = PR * C * PB := by
    unfold runOp
    rw [chainOp_sandwich _ PR PB q (liftU e ∘ F.U) (routeAdv F p).U fun _ => rfl,
      oracleU_eq_permUnitary, ← Submonoid.coe_mul, ← Submonoid.coe_mul, permUnitary_mul,
      permUnitary_mul]
    rfl
  have hC : C * kr e F.init.val (routeAncState m n) =
      kr e (R' * F.init.val) (routeAncState m n) :=
    chainOp_routeQuery_kr p H q F.U _
  have hCr : ∀ X, kr e X (routeAncState m n) * Cᴴ = kr e (X * R'ᴴ) (routeAncState m n) := by
    intro X
    have h := congrArg conjTranspose (chainOp_routeQuery_kr p H q F.U Xᴴ)
    rwa [conjTranspose_mul, kr_conjTranspose, kr_conjTranspose, conjTranspose_conjTranspose,
      routeAncState_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose] at h
  have c1 : ∀ X : Matrix _ _ ℂ, PRᴴ * (PR * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hPR, star_permUnitary_mul, Matrix.one_mul]
  have c2 : ∀ X : Matrix _ _ ℂ, PB * (PBᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hPB, permUnitary_mul_conjTranspose, Matrix.one_mul]
  unfold prOut prTrue_Q
  rw [run_branch_true, run_branch_true, hrun]
  congr 2
  have hW : (routeAdv F p).final * (PR * C * PB) * (routeAdv F p).init.val *
      ((routeAdv F p).final * (PR * C * PB))ᴴ =
      PR * (kr e F.final 1 * (C * kr e F.init.val (routeAncState m n) * Cᴴ) *
        (kr e F.final 1)ᴴ) * PRᴴ := by
    change PR * kr e F.final 1 * PRᴴ * (PR * C * PB) *
      (PBᴴ * kr e F.init.val (routeAncState m n) * PB) *
      (PR * kr e F.final 1 * PRᴴ * (PR * C * PB))ᴴ = _
    simp only [conjTranspose_mul, Matrix.mul_assoc, c1, c2]
  rw [hW, hPR, permUnitary_conj, trace_submatrix_equiv', hC, hCr, kr_conjTranspose,
    conjTranspose_one, kr_mul, kr_mul, trace_kr, one_mul, mul_one, trace_routeAncState, mul_one,
    F.final_conjTranspose]
  simp only [conjTranspose_mul, F.final_conjTranspose, Matrix.mul_assoc]
  rfl

/-- The index of the register of `F` in a basis state of the routed adversary, read after the
    router. -/
def routeBase (p : Fin m → Option (Fin n)) (i : Fin (m * n * (w * (2 * (m * n))))) :
    Fin (m * n * w) :=
  oracleIndex m n w
    ((ancRegIdx (routeAncE m n)).symm ((routePerm (fun x => (p x).isSome)).symm i)).1

/-- A diagonal final test of the routed adversary that reads the register of `F` through
    `routeBase` is the routed adversary of `F` with that test. -/
theorem routeAdv_withFinalB (F : QAdv m n w q) (p : Fin m → Option (Fin n))
    (g : Fin (m * n * w) → Bool) :
    (routeAdv F p).withFinalB (fun i => g (routeBase p i)) = routeAdv (F.withFinalB g) p := by
  simp only [QAdv.withFinalB, routeAdv]
  congr 1
  rw [permUnitary_conj]
  ext i j
  set G : Fin m → Bool := fun x => (p x).isSome with hG
  obtain ⟨⟨t, b⟩, rfl⟩ : ∃ u, routePerm (n := n) (w := w) G (ancRegIdx (routeAncE m n) u) = i :=
    ⟨(ancRegIdx (routeAncE m n)).symm ((routePerm G).symm i), by simp⟩
  obtain ⟨⟨t', b'⟩, rfl⟩ : ∃ u, routePerm (n := n) (w := w) G (ancRegIdx (routeAncE m n) u) = j :=
    ⟨(ancRegIdx (routeAncE m n)).symm ((routePerm G).symm j), by simp⟩
  have hb : ∀ u, routeBase p (routePerm (n := n) (w := w) G (ancRegIdx (routeAncE m n) u)) =
      oracleIndex m n w u.1 := fun u => by simp [routeBase, hG]
  rw [Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    kr_ancRegIdx_apply]
  simp only [diagB, Matrix.diagonal_apply, hb, Matrix.one_apply,
    (routePerm (n := n) (w := w) G).injective.eq_iff, (ancRegIdx (routeAncE m n)).injective.eq_iff,
    (oracleIndex m n w).injective.eq_iff, (routeAncE m n).injective.eq_iff, Prod.mk.injEq]
  by_cases h1 : t = t' <;> by_cases h2 : b = b' <;> simp [h1, h2]

end RouteAdv

/-! ## The no-message game -/

section NMA

variable {m n w q : ℕ} {Msg PK SK Sig X Y : Type}

/-- A no-message adversary: a query adversary with plain access to the hash, and the forgery
    read from a basis state of its register, `none` for no forgery. -/
structure QNMAAdv (m n w q : ℕ) (Msg Sig : Type) where
  /-- The query adversary; its final projector is not read by the game. -/
  adv : QAdv m n w q
  /-- The forgery of a basis state. -/
  forge : Fin (m * n * w) → Option (Msg × Sig)

/-- The winning test of the no-message game at the oracle `H`: the forgery of the basis state
    verifies under `hashOf eX eY H`. -/
def nmaTest (S : QROMSig Msg PK SK Sig X Y) (eX : X ≃ Fin m) (eY : Y ≃ Fin n) (pk : PK)
    (B : QNMAAdv m n w q Msg Sig) (H : Fin m → Fin n) (i : Fin (m * n * w)) : Bool :=
  (B.forge i).elim false fun f => S.verifyH (hashOf eX eY H) pk f.1 f.2

variable [NeZero n]

/-- The winning probability of the no-message adversary `B` at the public key `pk`, averaged
    over a uniform oracle. -/
def prNMA (S : QROMSig Msg PK SK Sig X Y) (eX : X ≃ Fin m) (eY : Y ≃ Fin n) (pk : PK)
    (B : QNMAAdv m n w q Msg Sig) : ℝ≥0∞ :=
  ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
    prOut (B.adv.withFinalB (nmaTest S eX eY pk B H)) H

/-- The no-message advantage of a randomized no-message adversary `B` with uniform coins `Ω` at
    the public key `pk`. -/
def qNMAProgAdvantage {Ω : Type} [Fintype Ω] (S : QROMSig Msg PK SK Sig X Y) (eX : X ≃ Fin m)
    (eY : Y ≃ Fin n) (pk : PK) (B : Ω → QNMAAdv m n w q Msg Sig) : ℝ≥0∞ :=
  ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * prNMA S eX eY pk (B ω)

end NMA

/-! ## The games of the CMA-to-NMA step -/

section Games

variable {κ : ℕ} {Msg : Type} {T m n c a : ℕ}

/-- The output of the `κ` attempts of one pair at the prover randomness–challenge pairs `v`. -/
def pairOut (P : Sigma) (x : P.Stmt) (w : P.Wit) (v : Fin κ → P.Rand × P.Ch) :
    Option (P.Com × P.Ch × P.Resp) :=
  firstSome fun i => fsAttempt P x w (v i).1 (v i).2

/-- The outputs of all pairs at the pair coins `u`. -/
def pairsOut (P : Sigma) (x : P.Stmt) (w : P.Wit) (u : Msg × Fin T → Fin κ → P.Rand × P.Ch) :
    Msg × Fin T → Option (P.Com × P.Ch × P.Resp) :=
  fun y => pairOut P x w (u y)

/-- The output of `κ` simulated attempts at the simulator randomness–challenge pairs `v`. -/
def pairSimOut (P : Sigma) (x : P.Stmt) (v : Fin κ → P.SimRand × P.Ch) :
    Option (P.Com × P.Ch × P.Resp) :=
  firstSome fun i => fsSimAttempt P x (v i).1 (v i).2

/-- The attempt entries of all pairs: row `j` holds, for attempt `i` of the pair `eQ.symm j`
    at `u (eQ.symm j) i`, its point `(μ, a_i)` encoded by `eX` and its challenge encoded by
    `eY`. -/
def attRows (P : Sigma) (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (x : P.Stmt) (w : P.Wit)
    (u : Msg × Fin T → Fin κ → P.Rand × P.Ch) : Fin c → Fin κ → Option (Fin m × Fin n) :=
  fun j i => some (eX ((eQ.symm j).1, P.commit x w (u (eQ.symm j) i).1), eY (u (eQ.symm j) i).2)

/-- The accepted entries of the outputs `o`: entry `j` is the point and the challenge of the
    accepted transcript of the pair `eQ.symm j`, nothing if its attempts are all rejected. -/
def accRow (P : Sigma) (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (o : Msg × Fin T → Option (P.Com × P.Ch × P.Resp)) :
    Fin c → Option (Fin m × Fin n) :=
  fun j => (o (eQ.symm j)).map fun t => (eX ((eQ.symm j).1, t.1), eY t.2.1)

/-- The signing table of the outputs `o`: the round outcome `j` is answered by the encoding of
    the challenge and response of the output of the pair `eQ.symm j`. -/
def outTab (P : Sigma) (eQ : Msg × Fin T ≃ Fin c) (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (o : Msg × Fin T → Option (P.Com × P.Ch × P.Resp)) : Fin c → Fin a :=
  fun j => eA ((o (eQ.symm j)).map fun t => (t.2.1, t.2.2))

/-- The points of the attempts other than the accepted one, over all pairs: the commitments
    `nonAccCom` of the pair `eQ.symm j` at its message, encoded by `eX`. -/
def nonAccPts (P : Sigma) (eX : Msg × P.Com ≃ Fin m) (eQ : Msg × Fin T ≃ Fin c) (x : P.Stmt)
    (w : P.Wit) (u : Msg × Fin T → Fin κ → P.Rand × P.Ch) : Finset (Fin m) :=
  Finset.univ.biUnion fun j =>
    (nonAccCom P x w (u (eQ.symm j))).image fun a => eX ((eQ.symm j).1, a)

variable {wd q k : ℕ}

/-- The winning probability of `A` at the public key `pk` with the signing table `f`, the
    oracle `H'` (read by the adversary and by the forgery test) and the additional final
    condition `b` on the basis states. -/
def prWinProg [DecidableEq Msg] [NeZero n] [NeZero c] {PK SK Sig X Y : Type}
    (S : QROMSig Msg PK SK Sig X Y) (eX : X ≃ Fin m) (eY : Y ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (A : QSigAdv m n wd q k c a T Msg PK Sig) (pk : PK)
    (f : Fin c → Fin a) (H' : Fin m → Fin n) (b : Fin (m * n * ancW c k wd) → Bool) : ℝ≥0∞ :=
  prOut ((toQAdv (A.run pk) f).withFinalB fun i =>
    forgeTest S eY eQ A pk i (H' (forgePoint S eX A pk i)) && b i) H'

/-- The basis states whose forgery point is not an accepted point of the outputs `o`. -/
def notAccFinal (P : Sigma) (recom : P.Stmt → P.Ch → P.Resp → P.Com) (eX : Msg × P.Com ≃ Fin m)
    (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp)) (x : P.Stmt)
    (o : Msg × Fin T → Option (P.Com × P.Ch × P.Resp)) : Fin (m * n * ancW c k wd) → Bool :=
  fun i => !decide (∃ j, (accRow P eX eY eQ o j).map Prod.fst =
    some (forgePoint (fsAbortSig P κ Msg recom) eX A x i))

variable [Fintype Msg] [DecidableEq Msg] [NeZero n] [NeZero c]

/-- G0*: the EUF-CMA game at the key `(x, w)` with the oracle `prog2 (attRows …) H`, the
    uniform `H` overwritten at the `κ` attempt points of every pair by the challenges of the
    pair coins `u`; the signer reads this oracle. -/
def fsG0s (P : Sigma) (recom : P.Stmt → P.Ch → P.Resp → P.Com) (eX : Msg × P.Com ≃ Fin m)
    (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp)) (x : P.Stmt) (w : P.Wit) :
    ℝ≥0∞ :=
  ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
    (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ *
      ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
        prForge (fsAbortSig P κ Msg recom) eX eY eQ eA A (x, (x, w))
          (prog2 (attRows P eX eY eQ x w u) H) fun y i => (u y i).1

/-- G1: as G0*, the signer of each pair reading the challenges of its own coins. -/
def fsG1 (P : Sigma) (recom : P.Stmt → P.Ch → P.Resp → P.Com) (eX : Msg × P.Com ≃ Fin m)
    (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp)) (x : P.Stmt) (w : P.Wit) :
    ℝ≥0∞ :=
  ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
    (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ *
      ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
        prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x
          (outTab P eQ eA (pairsOut P x w u)) (prog2 (attRows P eX eY eQ x w u) H)
          fun _ => true

/-- G1 restricted to the forgeries outside the accepted points. -/
def fsG1nb (P : Sigma) (recom : P.Stmt → P.Ch → P.Resp → P.Com) (eX : Msg × P.Com ≃ Fin m)
    (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp)) (x : P.Stmt) (w : P.Wit) :
    ℝ≥0∞ :=
  ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
    (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ *
      ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
        prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x
          (outTab P eQ eA (pairsOut P x w u)) (prog2 (attRows P eX eY eQ x w u) H)
          (notAccFinal (κ := κ) P recom eX eY eQ A x (pairsOut P x w u))

/-- The programmed game of the outputs `o` of all pairs: the uniform oracle programmed at the
    accepted entries of `o`, the signing table of `o`, and the forgeries outside the accepted
    points. -/
def fsProgWin (P : Sigma) (recom : P.Stmt → P.Ch → P.Resp → P.Com) (eX : Msg × P.Com ≃ Fin m)
    (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp)) (x : P.Stmt)
    (o : Msg × Fin T → Option (P.Com × P.Ch × P.Resp)) : ℝ≥0∞ :=
  ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
    prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x (outTab P eQ eA o)
      (prog1 (accRow P eX eY eQ o) H) (notAccFinal (κ := κ) P recom eX eY eQ A x o)

/-- G2: the programmed game of the honest outputs; the oracle values at the points of the
    attempts other than the accepted ones are fresh. -/
def fsG2 (P : Sigma) (recom : P.Stmt → P.Ch → P.Resp → P.Com) (eX : Msg × P.Com ≃ Fin m)
    (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp)) (x : P.Stmt) (w : P.Wit) :
    ℝ≥0∞ :=
  ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
    (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ *
      fsProgWin (κ := κ) P recom eX eY eQ eA A x (pairsOut P x w u)

/-- G3: the programmed game of the simulated outputs, `κ` simulated attempts per pair; it
    depends on the statement only. -/
def fsG3 (P : Sigma) (recom : P.Stmt → P.Ch → P.Resp → P.Com) (eX : Msg × P.Com ≃ Fin m)
    (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp)) (x : P.Stmt) : ℝ≥0∞ :=
  ∑ s : Msg × Fin T → Fin κ → P.SimRand × P.Ch,
    (Fintype.card (Msg × Fin T → Fin κ → P.SimRand × P.Ch) : ℝ≥0∞)⁻¹ *
      fsProgWin (κ := κ) P recom eX eY eQ eA A x fun y => pairSimOut P x (s y)

/-- The split of the pair coins into the prover randomness and the challenges, the challenges
    reindexed by `eQ` and encoded by `eY`. -/
def coinSplit (P : Sigma) (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) :
    (Msg × Fin T → Fin κ → P.Rand × P.Ch) ≃
      (Msg × Fin T → Fin κ → P.Rand) × (Fin c → Fin κ → Fin n) where
  toFun u := (fun y i => (u y i).1, fun j i => eY (u (eQ.symm j) i).2)
  invFun p := fun y i => (p.1 y i, eY.symm (p.2 (eQ y) i))
  left_inv u := by
    funext y i
    simp
  right_inv p := by
    refine Prod.ext ?_ ?_
    · rfl
    · funext j i
      simp

/-- G0 = G0*: the EUF-CMA game at the key `(x, w)` equals G0*, since the uniform oracle
    overwritten at the attempt points by fresh uniform challenges is uniform and independent of
    the prover randomness (`sum_prog2_eq`). -/
theorem fsG0_eq_fsG0s (P : Sigma) (recom : P.Stmt → P.Ch → P.Resp → P.Com)
    (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp)) (x : P.Stmt) (w : P.Wit) :
    ∑ R : Msg × Fin T → Fin κ → P.Rand,
        (Fintype.card (Msg × Fin T → Fin κ → P.Rand) : ℝ≥0∞)⁻¹ *
          ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
            prForge (fsAbortSig P κ Msg recom) eX eY eQ eA A (x, (x, w)) H R =
      fsG0s (κ := κ) P recom eX eY eQ eA A x w := by
  set F : (Msg × Fin T → Fin κ → P.Rand) → (Fin m → Fin n) → ℝ≥0∞ := fun R H =>
    (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
      prForge (fsAbortSig P κ Msg recom) eX eY eQ eA A (x, (x, w)) H R with hF
  have hrows : ∀ (R : Msg × Fin T → Fin κ → P.Rand) (c' : Fin c → Fin κ → Fin n),
      attRows P eX eY eQ x w ((coinSplit P eY eQ).symm (R, c')) =
      fun j i => some (eX ((eQ.symm j).1, P.commit x w (R (eQ.symm j) i)), c' j i) := by
    intro R c'
    funext j i
    simp [attRows, coinSplit]
  have hcard : (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ *
      (Fintype.card (Fin c → Fin κ → Fin n) : ℝ≥0∞) =
        (Fintype.card (Msg × Fin T → Fin κ → P.Rand) : ℝ≥0∞)⁻¹ := by
    rw [Fintype.card_congr (coinSplit P eY eQ), Fintype.card_prod, Nat.cast_mul,
      ENNReal.mul_inv (by simp) (by simp), mul_assoc,
      ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (by simp), mul_one]
  unfold fsG0s
  rw [← (coinSplit P eY eQ).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun R _ => ?_
  have hR : ∀ c' : Fin c → Fin κ → Fin n,
      (fun y i => ((coinSplit P eY eQ).symm (R, c') y i).1) = R := fun _ => rfl
  simp only [hrows, hR]
  symm
  rw [← Finset.mul_sum]
  have key := sum_prog2_eq (fun j i => eX ((eQ.symm j).1, P.commit x w (R (eQ.symm j) i)))
    (F R)
  simp only [hF] at key
  rw [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hcard]

/-- G2 = G3 under zero HVZK distance at `(x, w)`: the programmed game is a function of the
    outputs of the pairs, whose honest and simulated laws agree (`fsAborts_pairs_sim_eq`). -/
theorem fsG2_eq_fsG3 {P : Sigma} {x : P.Stmt} {w : P.Wit} (hzk : P.hvzkDistAt x w = 0)
    (recom : P.Stmt → P.Ch → P.Resp → P.Com) (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp)) :
    fsG2 (κ := κ) P recom eX eY eQ eA A x w = fsG3 (κ := κ) P recom eX eY eQ eA A x :=
  fsAborts_pairs_sim_eq hzk κ (fsProgWin (κ := κ) P recom eX eY eQ eA A x)

omit [Fintype Msg] [DecidableEq Msg] [NeZero n] [NeZero c] in
/-- At a point `z` outside the points `(μ, a)` of the attempts other than the accepted one,
    the first attempt entry of a pair at `z` is its accepted entry. -/
theorem firstSome_att_eq_acc (P : Sigma) (x : P.Stmt) (w : P.Wit) (eX : Msg × P.Com ≃ Fin m)
    (eY : P.Ch ≃ Fin n) (μ : Msg) (z : Fin m) : ∀ {N : ℕ} (v : Fin N → P.Rand × P.Ch),
    (∀ a ∈ nonAccCom P x w v, eX (μ, a) ≠ z) →
    (firstSome fun i => matchAt z (some (eX (μ, P.commit x w (v i).1), eY (v i).2))) =
      matchAt z ((pairOut P x w v).map fun t => (eX (μ, t.1), eY t.2.1))
  | 0, _, _ => rfl
  | N + 1, v, h => by
    by_cases hacc : (fsAttempt P x w (v 0).1 (v 0).2).isSome
    · have hnac : nonAccCom P x w v =
          Finset.univ.image fun i => P.commit x w (Fin.tail v i).1 := by
        simp [nonAccCom, hacc]
      have hacc' : P.accept (P.respond x w (v 0).1 (v 0).2) = true := by
        by_contra hn
        simp [fsAttempt, hn] at hacc
      have hout : pairOut P x w v =
          some (P.commit x w (v 0).1, (v 0).2, P.respond x w (v 0).1 (v 0).2) := by
        simp [pairOut, firstSome, fsAttempt, hacc']
      have htail : ∀ i : Fin N,
          matchAt z (some (eX (μ, P.commit x w (v i.succ).1), eY (v i.succ).2)) = none := by
        intro i
        have := h _ (by rw [hnac]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i))
        simp only [matchAt, Option.bind_some, ite_eq_right_iff, reduceCtorEq, imp_false]
        exact this
      rw [hout]
      simp only [firstSome]
      rw [firstSome_eq_none
        (Fin.tail fun i => matchAt z (some (eX (μ, P.commit x w (v i).1), eY (v i).2))) htail]
      simp
    · have hnone : fsAttempt P x w (v 0).1 (v 0).2 = none := Option.not_isSome_iff_eq_none.mp hacc
      have hnac : nonAccCom P x w v =
          insert (P.commit x w (v 0).1) (nonAccCom P x w (Fin.tail v)) := by
        simp [nonAccCom, hnone]
      have h0 : eX (μ, P.commit x w (v 0).1) ≠ z :=
        h _ (by rw [hnac]; exact Finset.mem_insert_self _ _)
      have ih := firstSome_att_eq_acc P x w eX eY μ z (Fin.tail v) fun a ha =>
        h a (by rw [hnac]; exact Finset.mem_insert_of_mem ha)
      have hout : pairOut P x w v = pairOut P x w (Fin.tail v) := by
        simp only [pairOut, firstSome, hnone, Option.none_or]
        rfl
      rw [hout, ← ih]
      simp only [firstSome]
      simp [matchAt, h0]
      rfl

omit [Fintype Msg] [DecidableEq Msg] [NeZero n] [NeZero c] in
/-- The oracles of G1 and G2 agree outside the points of the attempts other than the accepted
    ones. -/
theorem prog2_attRows_eq_prog1_accRow (P : Sigma) (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (x : P.Stmt) (w : P.Wit)
    (u : Msg × Fin T → Fin κ → P.Rand × P.Ch) (H : Fin m → Fin n) (z : Fin m)
    (hz : z ∉ nonAccPts P eX eQ x w u) :
    prog2 (attRows P eX eY eQ x w u) H z =
      prog1 (accRow P eX eY eQ (pairsOut P x w u)) H z := by
  unfold prog2 prog1
  congr 2
  funext j
  refine firstSome_att_eq_acc P x w eX eY (eQ.symm j).1 z (u (eQ.symm j)) fun a ha he => ?_
  exact hz (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_image.mpr ⟨a, ha, he⟩⟩)

omit [NeZero n] [NeZero c] in
open Classical in
/-- Given the outputs `o` of all pairs, the commitment `a₀` is among the commitments of the
    attempts of the pair `y₀` other than the accepted one with probability at most
    `κ (ρ ⊔ ε)`: the pairs are independent and `rejected_mem_cond_le` holds at `y₀`. -/
theorem sum_pairsOut_nonAcc_le (P : Sigma) (x : P.Stmt) (w : P.Wit)
    (o : Msg × Fin T → Option (P.Com × P.Ch × P.Resp)) (y₀ : Msg × Fin T) (a₀ : P.Com) :
    ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
        (if pairsOut P x w u = o then (1 : ℝ≥0∞) else 0) *
          (if a₀ ∈ nonAccCom P x w (u y₀) then 1 else 0) ≤
      κ * (P.rejCommitDistAt x w ⊔ P.commitDistAt x w) *
        ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
          (if pairsOut P x w u = o then (1 : ℝ≥0∞) else 0) := by
  classical
  set lam := (κ : ℝ≥0∞) * (P.rejCommitDistAt x w ⊔ P.commitDistAt x w) with hlam
  set G' : Msg × Fin T → (Fin κ → P.Rand × P.Ch) → ℝ≥0∞ := fun y v =>
    if pairOut P x w v = o y then 1 else 0 with hG'
  set G : Msg × Fin T → (Fin κ → P.Rand × P.Ch) → ℝ≥0∞ := fun y v =>
    G' y v * (if y = y₀ then (if a₀ ∈ nonAccCom P x w v then 1 else 0) else 1) with hG
  have hout : ∀ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
      (if pairsOut P x w u = o then (1 : ℝ≥0∞) else 0) = ∏ y, G' y (u y) := by
    intro u
    rw [Finset.prod_boole]
    simp [pairsOut, funext_iff]
  have hlhs : ∀ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
      (if pairsOut P x w u = o then (1 : ℝ≥0∞) else 0) *
          (if a₀ ∈ nonAccCom P x w (u y₀) then 1 else 0) = ∏ y, G y (u y) := by
    intro u
    rw [hout, hG, Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  rw [Finset.sum_congr rfl fun u _ => hlhs u, Finset.sum_congr rfl fun u _ => hout u,
    ← Fintype.prod_sum, ← Fintype.prod_sum]
  calc ∏ y, ∑ v, G y v ≤ ∏ y, ((if y = y₀ then lam else 1) * ∑ v, G' y v) := by
        refine Finset.prod_le_prod fun y _ => ?_
        by_cases hy : y = y₀
        · subst hy
          have := rejected_mem_cond_le x w (o y) a₀ κ
          simp only [hG, hG', ite_true]
          exact this
        · simp [hG, hy]
    _ = lam * ∏ y, ∑ v, G' y v := by
        rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
        simp

omit [NeZero n] [NeZero c] in
open Classical in
/-- Given the outputs `o` of all pairs, a point `z` is among the points of the attempts other
    than the accepted ones with probability at most `T κ (ρ ⊔ ε)`: a point has one message and
    `T` pairs. -/
theorem sum_pairsOut_nonAccPts_le (P : Sigma) (eX : Msg × P.Com ≃ Fin m)
    (eQ : Msg × Fin T ≃ Fin c) (x : P.Stmt) (w : P.Wit)
    (o : Msg × Fin T → Option (P.Com × P.Ch × P.Resp)) (z : Fin m) :
    ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
        (if pairsOut P x w u = o then (1 : ℝ≥0∞) else 0) *
          (if z ∈ nonAccPts P eX eQ x w u then 1 else 0) ≤
      T * (κ * (P.rejCommitDistAt x w ⊔ P.commitDistAt x w)) *
        ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
          (if pairsOut P x w u = o then (1 : ℝ≥0∞) else 0) := by
  have hpt : ∀ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
      (if z ∈ nonAccPts P eX eQ x w u then (1 : ℝ≥0∞) else 0) ≤
        ∑ τ : Fin T, if (eX.symm z).2 ∈ nonAccCom P x w (u ((eX.symm z).1, τ)) then 1 else 0 := by
    intro u
    split_ifs with hz
    · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hz
      obtain ⟨a', ha', he⟩ := Finset.mem_image.mp hj
      have hs : eX.symm z = ((eQ.symm j).1, a') := by rw [← he]; simp
      refine le_trans ?_ (Finset.single_le_sum (f := fun τ : Fin T =>
        if (eX.symm z).2 ∈ nonAccCom P x w (u ((eX.symm z).1, τ)) then (1 : ℝ≥0∞) else 0)
        (fun _ _ => bot_le) (Finset.mem_univ (eQ.symm j).2))
      simp [hs, ha']
    · exact bot_le
  calc _ ≤ ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
          (if pairsOut P x w u = o then (1 : ℝ≥0∞) else 0) *
            ∑ τ : Fin T, if (eX.symm z).2 ∈ nonAccCom P x w (u ((eX.symm z).1, τ)) then 1 else 0 :=
        Finset.sum_le_sum fun u _ => by gcongr; exact hpt u
    _ = ∑ τ : Fin T, ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
          (if pairsOut P x w u = o then (1 : ℝ≥0∞) else 0) *
            (if (eX.symm z).2 ∈ nonAccCom P x w (u ((eX.symm z).1, τ)) then 1 else 0) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ _τ : Fin T, κ * (P.rejCommitDistAt x w ⊔ P.commitDistAt x w) *
          ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
            (if pairsOut P x w u = o then (1 : ℝ≥0∞) else 0) :=
        Finset.sum_le_sum fun τ _ => sum_pairsOut_nonAcc_le P x w o _ _
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The adversary of the forgery test with the signing table `fb.1` inside it and the
    additional final condition `fb.2`, as a general multi-round adversary without rounds with
    `flatQ q k q + 1` queries. -/
def winAdv [NeZero m] {PK SK Sig X Y : Type} (S : QROMSig Msg PK SK Sig X Y) (eX : X ≃ Fin m)
    (eY : Y ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) (A : QSigAdv m n wd q k c a T Msg PK Sig)
    (pk : PK) (fb : (Fin c → Fin a) × (Fin (m * n * ancW c k wd) → Bool)) :
    QAdvMRGen m n (ancW c k wd * (m * n)) (flatQ q k q + 1) 0 1 1 :=
  (finalQAdv (toQAdv (A.run pk) fb.1) (forgePoint S eX A pk) fun i θ =>
    forgeTest S eY eQ A pk i θ && fb.2 i).toMR.toGen

omit [Fintype Msg] in
/-- `prWinProg` is the acceptance probability of `winAdv` at the oracle. -/
theorem prWinProg_eq_prOutMRGen [NeZero m] {PK SK Sig X Y : Type}
    (S : QROMSig Msg PK SK Sig X Y) (eX : X ≃ Fin m) (eY : Y ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (A : QSigAdv m n wd q k c a T Msg PK Sig) (pk : PK)
    (f : Fin c → Fin a) (H' : Fin m → Fin n) (b : Fin (m * n * ancW c k wd) → Bool) :
    prWinProg S eX eY eQ A pk f H' b =
      prOutMRGen (winAdv S eX eY eQ A pk (f, b)) H' fun _ => 0 := by
  rw [winAdv, prOutMRGen_toMR_toGen]
  unfold prWinProg
  exact prOut_withFinalB_eq_prOut_finalQAdv (toQAdv (A.run pk) f) (forgePoint S eX A pk)
    (fun i θ => forgeTest S eY eQ A pk i θ && b i) H'

/-- G1 to G2 for the forgeries outside the accepted points: the oracles agree outside the
    points of the attempts other than the accepted ones, a set of conditional probability at
    most `T κ (ρ ⊔ ε)` given the outputs of all pairs, hence given the adversary, the signing
    table and the oracle of G2; gentle resampling (`prOutMRGen_resample_gentle_fiber_le`)
    with the forgery test as one extra query. -/
theorem fsG1nb_fsG2_le [NeZero m] (P : Sigma) (recom : P.Stmt → P.Ch → P.Resp → P.Com)
    (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp)) (x : P.Stmt) (w : P.Wit) :
    absDiff (fsG1nb (κ := κ) P recom eX eY eQ eA A x w) (fsG2 (κ := κ) P recom eX eY eQ eA A x w) ≤
      2 * ((flatQ q k q + 1 : ℕ) : ℝ≥0∞) *
        ((T : ℝ≥0∞) * (κ * (P.rejCommitDistAt x w ⊔ P.commitDistAt x w))) ^ (1 / 2 : ℝ) := by
  classical
  set NU := (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ with hNU
  set NH := (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ with hNH
  set lam := (T : ℝ≥0∞) * (κ * (P.rejCommitDistAt x w ⊔ P.commitDistAt x w)) with hlam
  set ind : (Msg × Fin T → Fin κ → P.Rand × P.Ch) × (Fin m → Fin n) →
      (Fin c → Fin a) × (Fin (m * n * ancW c k wd) → Bool) := fun ω =>
    (outTab P eQ eA (pairsOut P x w ω.1),
      notAccFinal (κ := κ) P recom eX eY eQ A x (pairsOut P x w ω.1)) with hind
  set H₂ : (Msg × Fin T → Fin κ → P.Rand × P.Ch) × (Fin m → Fin n) → Fin m → Fin n :=
    fun ω => prog1 (accRow P eX eY eQ (pairsOut P x w ω.1)) ω.2 with hH₂
  have hsum : ∀ G : (Msg × Fin T → Fin κ → P.Rand × P.Ch) × (Fin m → Fin n) → ℝ≥0∞,
      ∑ u, NU * ∑ H, NH * G (u, H) = ∑ ω, NU * NH * G ω := by
    intro G
    rw [Fintype.sum_prod_type]
    simp only [Finset.mul_sum, mul_assoc]
  have hμ : ∑ _ω : (Msg × Fin T → Fin κ → P.Rand × P.Ch) × (Fin m → Fin n), NU * NH = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul,
      mul_mul_mul_comm, ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _),
      ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _), one_mul]
  have hcol : ∀ (o : Msg × Fin T → Option (P.Com × P.Ch × P.Resp)) (H₀ : Fin m → Fin n)
      (F : (Msg × Fin T → Fin κ → P.Rand × P.Ch) → ℝ≥0∞),
      ∑ ω : (Msg × Fin T → Fin κ → P.Rand × P.Ch) × (Fin m → Fin n),
          NU * NH * (if (pairsOut P x w ω.1, ω.2) = (o, H₀) then 1 else 0) * F ω.1 =
        NU * NH * ∑ u, (if pairsOut P x w u = o then 1 else 0) * F u := by
    intro o H₀ F
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : pairsOut P x w u = o <;> simp [hu, Prod.mk.injEq]
  have hsparse : ∀ (j : (Fin c → Fin a) × (Fin (m * n * ancW c k wd) → Bool)) (z : Fin m)
      (h : Fin m → Fin n) (g : Fin 1 → Fin 1),
      ∑ ω, NU * NH * (if ind ω = j ∧ H₂ ω = h ∧ (fun _ : Fin 1 => (0 : Fin 1)) = g ∧
          z ∈ nonAccPts P eX eQ x w ω.1 then 1 else 0) ≤
        lam * ∑ ω, NU * NH * (if ind ω = j ∧ H₂ ω = h ∧ (fun _ : Fin 1 => (0 : Fin 1)) = g
          then 1 else 0) := by
    intro j z h g
    have hsplit : ∀ ω, NU * NH * (if ind ω = j ∧ H₂ ω = h ∧
        (fun _ : Fin 1 => (0 : Fin 1)) = g ∧ z ∈ nonAccPts P eX eQ x w ω.1 then 1 else 0) =
        NU * NH * (if z ∈ nonAccPts P eX eQ x w ω.1 then 1 else 0) *
          (if ind ω = j ∧ H₂ ω = h ∧ (fun _ : Fin 1 => (0 : Fin 1)) = g then 1 else 0) := by
      intro ω
      by_cases hz : z ∈ nonAccPts P eX eQ x w ω.1 <;> simp [hz]
    simp only [hsplit]
    refine sum_mul_boole_mul_le_of_fiber (fun ω => (pairsOut P x w ω.1, ω.2)) _ _ _ lam ?_ ?_
    · intro ω ω' he
      simp only [Prod.mk.injEq] at he
      simp only [hind, hH₂, he.1, he.2]
    · intro ω₀
      have h1 := hcol (pairsOut P x w ω₀.1) ω₀.2
        fun u => if z ∈ nonAccPts P eX eQ x w u then 1 else 0
      have h2 := hcol (pairsOut P x w ω₀.1) ω₀.2 fun _ => 1
      simp only [mul_one] at h2
      have hc := sum_pairsOut_nonAccPts_le (κ := κ) P eX eQ x w (pairsOut P x w ω₀.1) z
      have h3 : NU * NH * ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
            (if pairsOut P x w u = pairsOut P x w ω₀.1 then 1 else 0) *
              (if z ∈ nonAccPts P eX eQ x w u then (1 : ℝ≥0∞) else 0) ≤
          lam * (NU * NH * ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
            if pairsOut P x w u = pairsOut P x w ω₀.1 then 1 else 0) := by
        rw [mul_left_comm]
        gcongr
      rw [← h1, ← h2] at h3
      convert h3
  have key := prOutMRGen_resample_gentle_fiber_le
    (winAdv (fsAbortSig P κ Msg recom) eX eY eQ A x) ind (fun _ => NU * NH) hμ
    (fun ω => prog2 (attRows P eX eY eQ x w ω.1) ω.2) H₂ (fun _ _ => 0)
    (fun ω => nonAccPts P eX eQ x w ω.1) lam
    (fun ω z hz => prog2_attRows_eq_prog1_accRow P eX eY eQ x w ω.1 ω.2 z hz) hsparse
  have e1 : fsG1nb (κ := κ) P recom eX eY eQ eA A x w = ∑ ω, NU * NH *
      prOutMRGen (winAdv (fsAbortSig P κ Msg recom) eX eY eQ A x (ind ω))
        (prog2 (attRows P eX eY eQ x w ω.1) ω.2) fun _ => 0 := by
    rw [← hsum]
    simp only [fsG1nb, prWinProg_eq_prOutMRGen, hind, hNU, hNH]
  have e2 : fsG2 (κ := κ) P recom eX eY eQ eA A x w = ∑ ω, NU * NH *
      prOutMRGen (winAdv (fsAbortSig P κ Msg recom) eX eY eQ A x (ind ω)) (H₂ ω) fun _ => 0 := by
    rw [← hsum]
    simp only [fsG2, fsProgWin, prWinProg_eq_prOutMRGen, hind, hH₂, hNU, hNH]
  rw [e1, e2]
  exact key

/-! ### G0* to G1: collisions of the attempt points -/

omit [Fintype Msg] [DecidableEq Msg] [NeZero n] [NeZero c] in
/-- The number of prover randomnesses with commitment `a` is at most `commitDistAt` times the
    number of all. -/
theorem sum_rand_commit_le (P : Sigma) (x : P.Stmt) (w : P.Wit) (a : P.Com) :
    (∑ r : P.Rand, if P.commit x w r = a then (1 : ℝ≥0∞) else 0) ≤
      P.commitDistAt x w * Fintype.card P.Rand := by
  have h1 : (PMF.uniformFintype P.Rand).toOuterMeasure {r | P.commit x w r = a} =
      (∑ r : P.Rand, if P.commit x w r = a then (1 : ℝ≥0∞) else 0) *
        (Fintype.card P.Rand : ℝ≥0∞)⁻¹ := by
    rw [PMF.toOuterMeasure_apply, tsum_fintype, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [Set.indicator_apply]
  calc (∑ r : P.Rand, if P.commit x w r = a then (1 : ℝ≥0∞) else 0)
      = ((∑ r : P.Rand, if P.commit x w r = a then (1 : ℝ≥0∞) else 0) *
          (Fintype.card P.Rand : ℝ≥0∞)⁻¹) * Fintype.card P.Rand := by
        rw [mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
    _ ≤ P.commitDistAt x w * Fintype.card P.Rand := by
        gcongr
        rw [← h1]
        exact le_iSup (fun a : P.Com =>
          (PMF.uniformFintype P.Rand).toOuterMeasure {r | P.commit x w r = a}) a

omit [Fintype Msg] [DecidableEq Msg] [NeZero n] [NeZero c] in
/-- Among the vectors of `κ` prover randomnesses, the number whose entry `i` has the
    commitment `g v`, for `g` not reading the entry `i`, is at most `commitDistAt` times the
    number of all. -/
theorem sum_commit_coord_le (P : Sigma) (x : P.Stmt) (w : P.Wit) {N : ℕ} (i : Fin N)
    (g : (Fin N → P.Rand) → P.Com) (hg : ∀ v r, g (Function.update v i r) = g v) :
    (∑ v : Fin N → P.Rand, if P.commit x w (v i) = g v then (1 : ℝ≥0∞) else 0) ≤
      P.commitDistAt x w * Fintype.card (Fin N → P.Rand) := by
  have h := sum_mul_le_of_update i (fun _ => (1 : ℝ≥0∞))
    (fun v => if P.commit x w (v i) = g v then (1 : ℝ≥0∞) else 0) (P.commitDistAt x w)
    (fun _ _ => rfl) fun v => by
      simp only [Function.update_self, hg]
      exact sum_rand_commit_le P x w (g v)
  simpa using h

/-- A collision at the pair `y` of the prover randomness table `R`: an attempt of `y` has the
    commitment of another attempt of a pair with the message of `y`, so that the two attempt
    points agree. -/
def attCol (P : Sigma) (x : P.Stmt) (w : P.Wit) (R : Msg × Fin T → Fin κ → P.Rand)
    (y : Msg × Fin T) : Prop :=
  ∃ i τ i', ((y.1, τ), i') ≠ (y, i) ∧ P.commit x w (R (y.1, τ) i') = P.commit x w (R y i)

omit [Fintype Msg] [NeZero n] [NeZero c] in
open Classical in
/-- Given the prover randomness of the other pairs, a collision at the pair `y` has
    probability at most `T κ² ε`: each of the `κ` attempts of `y` meets each of the `T κ`
    attempts of the pairs of its message with probability at most `ε = commitDistAt`. -/
theorem sum_attCol_le (P : Sigma) (x : P.Stmt) (w : P.Wit) (R : Msg × Fin T → Fin κ → P.Rand)
    (y : Msg × Fin T) :
    (∑ v : Fin κ → P.Rand, if attCol P x w (Function.update R y v) y then (1 : ℝ≥0∞) else 0) ≤
      T * κ ^ 2 * P.commitDistAt x w * Fintype.card (Fin κ → P.Rand) := by
  set N := (Fintype.card (Fin κ → P.Rand) : ℝ≥0∞) with hN
  set F : Fin κ → Fin T → Fin κ → (Fin κ → P.Rand) → ℝ≥0∞ := fun i τ i' v =>
    if ((y.1, τ), i') ≠ (y, i) ∧
      P.commit x w (v i) = P.commit x w (Function.update R y v (y.1, τ) i') then 1 else 0
    with hF
  have hpt : ∀ v : Fin κ → P.Rand,
      (if attCol P x w (Function.update R y v) y then (1 : ℝ≥0∞) else 0) ≤
        ∑ i, ∑ τ, ∑ i', F i τ i' v := by
    intro v
    split_ifs with h
    · obtain ⟨i, τ, i', hne, he⟩ := h
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i))
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ τ))
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i'))
      simp only [hF]
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hne, by simpa using he.symm⟩)]
    · exact bot_le
  have hterm : ∀ i τ i', ∑ v, F i τ i' v ≤ P.commitDistAt x w * N := by
    intro i τ i'
    by_cases hne : ((y.1, τ), i') = (y, i)
    · simp only [hF]
      rw [Finset.sum_eq_zero fun v _ => ite_eq_right_of_eq_false _ _ (eq_false fun h => h.1 hne)]
      exact bot_le
    · refine le_trans (Finset.sum_le_sum fun v _ => ?_) (sum_commit_coord_le P x w i
        (fun v => P.commit x w (Function.update R y v (y.1, τ) i')) fun v r => ?_)
      · simp only [hF]
        split_ifs <;> simp_all
      · by_cases hy : (y.1, τ) = y
        · have hi : i' ≠ i := fun h => hne (by rw [hy, h])
          simp [hy, Function.update_of_ne hi]
        · simp [Function.update_of_ne hy]
  calc _ ≤ ∑ v, ∑ i, ∑ τ, ∑ i', F i τ i' v := Finset.sum_le_sum fun v _ => hpt v
    _ = ∑ i, ∑ τ, ∑ i', ∑ v, F i τ i' v := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ _i : Fin κ, ∑ _τ : Fin T, ∑ _i' : Fin κ, P.commitDistAt x w * N := by
        gcongr with i _ τ _ i' _
        exact hterm i τ i'
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

omit [Fintype Msg] [DecidableEq Msg] [NeZero n] [NeZero c] in
/-- Without a collision at the pair `y`, the oracle of G0* at the attempt point of attempt `i`
    of `y` is the challenge of that attempt. -/
theorem prog2_attRows_own (P : Sigma) (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (x : P.Stmt) (w : P.Wit)
    (u : Msg × Fin T → Fin κ → P.Rand × P.Ch) (H : Fin m → Fin n) (y : Msg × Fin T) (i : Fin κ)
    (hy : ¬ attCol P x w (fun y' i' => (u y' i').1) y) :
    prog2 (attRows P eX eY eQ x w u) H (eX (y.1, P.commit x w (u y i).1)) = eY (u y i).2 := by
  refine prog2_eq_of_unique _ H _ (eQ y) i _ (by simp [attRows]) fun j' i' hne => ?_
  simp only [attRows, matchAt, Option.bind_some, ite_eq_right_iff, reduceCtorEq, imp_false]
  intro he
  have he' := eX.injective he
  simp only [Prod.mk.injEq] at he'
  apply hy
  refine ⟨i, (eQ.symm j').2, i', fun hc => hne ?_, ?_⟩
  · simp only [Prod.mk.injEq] at hc
    have hj : eQ.symm j' = y := Prod.ext he'.1 (by simpa using congrArg Prod.snd hc.1)
    simp [← hj, hc.2]
  · have hj : ((y.1, (eQ.symm j').2) : Msg × Fin T) = eQ.symm j' := Prod.ext he'.1.symm rfl
    simpa [hj] using he'.2

omit [Fintype Msg] [DecidableEq Msg] [NeZero n] [NeZero c] in
/-- Without a collision at the pair `eQ.symm j`, the signing tables of G0* and G1 agree at
    the round outcome `j`. -/
theorem outTab_eq_signTab (P : Sigma) (recom : P.Stmt → P.Ch → P.Resp → P.Com)
    (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (P.Ch × P.Resp) ≃ Fin a) (x : P.Stmt) (w : P.Wit)
    (u : Msg × Fin T → Fin κ → P.Rand × P.Ch) (H : Fin m → Fin n) (j : Fin c)
    (hj : ¬ attCol P x w (fun y' i' => (u y' i').1) (eQ.symm j)) :
    outTab P eQ eA (pairsOut P x w u) j =
      signTab (fsAbortSig P κ Msg recom) eQ eA (x, w)
        (hashOf eX eY (prog2 (attRows P eX eY eQ x w u) H)) (fun y' i' => (u y' i').1) j := by
  have hown := fun i => prog2_attRows_own P eX eY eQ x w u H (eQ.symm j) i hj
  simp only [outTab, signTab, fsAbortSig, pairsOut, pairOut, hashOf, hown, Equiv.symm_apply_apply]

omit [NeZero c] in
/-- The prover randomness and the oracle of G0* are independent and uniform: averaged over the
    pair coins and the oracle, every function of the prover randomness and the programmed
    oracle has the average it has over a uniform prover randomness and a uniform oracle. -/
theorem sum_prog2_attRows_eq (P : Sigma) (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (x : P.Stmt) (w : P.Wit)
    (F : (Msg × Fin T → Fin κ → P.Rand) → (Fin m → Fin n) → ℝ≥0∞) :
    ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
        (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ *
          ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
            F (fun y i => (u y i).1) (prog2 (attRows P eX eY eQ x w u) H) =
      ∑ R : Msg × Fin T → Fin κ → P.Rand,
        (Fintype.card (Msg × Fin T → Fin κ → P.Rand) : ℝ≥0∞)⁻¹ *
          ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ * F R H := by
  have hrows : ∀ (R : Msg × Fin T → Fin κ → P.Rand) (c' : Fin c → Fin κ → Fin n),
      attRows P eX eY eQ x w ((coinSplit P eY eQ).symm (R, c')) =
      fun j i => some (eX ((eQ.symm j).1, P.commit x w (R (eQ.symm j) i)), c' j i) := by
    intro R c'
    funext j i
    simp [attRows, coinSplit]
  have hcard : (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ *
      (Fintype.card (Fin c → Fin κ → Fin n) : ℝ≥0∞) =
        (Fintype.card (Msg × Fin T → Fin κ → P.Rand) : ℝ≥0∞)⁻¹ := by
    rw [Fintype.card_congr (coinSplit P eY eQ), Fintype.card_prod, Nat.cast_mul,
      ENNReal.mul_inv (by simp) (by simp), mul_assoc,
      ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (by simp), mul_one]
  rw [← (coinSplit P eY eQ).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun R _ => ?_
  have hR : ∀ c' : Fin c → Fin κ → Fin n,
      (fun y i => ((coinSplit P eY eQ).symm (R, c') y i).1) = R := fun _ => rfl
  simp only [hrows, hR]
  rw [← Finset.mul_sum]
  have key := sum_prog2_eq (fun j i => eX ((eQ.symm j).1, P.commit x w (R (eQ.symm j) i)))
    fun H => (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ * F R H
  rw [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hcard]

omit [Fintype Msg] in
/-- `prForge` is the acceptance probability of the adversary that records its rounds, with
    the forgery test as its final projector. -/
theorem prForge_eq_recordGen {PK SK Sig X Y : Type} (S : QROMSig Msg PK SK Sig X Y)
    (eX : X ≃ Fin m) (eY : Y ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) (eA : Option Sig ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg PK Sig) (ks : PK × SK) (H : Fin m → Fin n)
    (R : Msg × Fin T → S.Coins) :
    prForge S eX eY eQ eA A ks H R =
      prOutMRGen (recordGen (A.run ks.1) fun i => forgeTest S eY eQ A ks.1 i
        (H (forgePoint S eX A ks.1 i))) H (signTab S eQ eA ks.2 (hashOf eX eY H) R) :=
  prOut_withFinalB_toQAdv_eq _ _ _ _

omit [Fintype Msg] in
/-- `prWinProg` without an additional final condition is the acceptance probability of the
    adversary that records its rounds, with the forgery test as its final projector. -/
theorem prWinProg_true_eq {PK SK Sig X Y : Type} (S : QROMSig Msg PK SK Sig X Y)
    (eX : X ≃ Fin m) (eY : Y ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (A : QSigAdv m n wd q k c a T Msg PK Sig) (pk : PK) (f : Fin c → Fin a)
    (H' : Fin m → Fin n) :
    prWinProg S eX eY eQ A pk f H' (fun _ => true) =
      prOutMRGen (recordGen (A.run pk) fun i => forgeTest S eY eQ A pk i
        (H' (forgePoint S eX A pk i))) H' f := by
  unfold prWinProg
  simp only [Bool.and_true]
  exact prOut_withFinalB_toQAdv_eq _ _ _ _

/-- G0* to G1: the signing tables of the two games differ only at the pairs with a collision
    of attempt points (`attCol`), an event of the prover randomness of the pair of probability
    at most `T κ² ε` given the oracle of G0* and the prover randomness of the other pairs
    (`sum_attCol_le`, `sum_prog2_attRows_eq`); the up-to-bad bound for the rounds
    (`rounds_upto_bad_local_dep`) with the forgery test, a function of the oracle, as the key
    of the adversary gives `k T κ² ε`. -/
theorem fsG0s_fsG1_le (P : Sigma) (recom : P.Stmt → P.Ch → P.Resp → P.Com)
    (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp)) (x : P.Stmt) (w : P.Wit) :
    absDiff (fsG0s (κ := κ) P recom eX eY eQ eA A x w) (fsG1 (κ := κ) P recom eX eY eQ eA A x w) ≤
      k * (T * κ ^ 2 * P.commitDistAt x w) := by
  classical
  set NU := (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ with hNU
  set NH := (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ with hNH
  set NR := (Fintype.card (Msg × Fin T → Fin κ → P.Rand) : ℝ≥0∞)⁻¹ with hNR
  set lam := (T : ℝ≥0∞) * κ ^ 2 * P.commitDistAt x w with hlam
  set S := fsAbortSig P κ Msg recom with hS
  set Gk : (Fin m → Fin n) → Fin (m * n * ancW c k wd) → Bool := fun h i =>
    forgeTest S eY eQ A x i (h (forgePoint S eX A x i)) with hGk
  set H₁ : (Msg × Fin T → Fin κ → P.Rand × P.Ch) × (Fin m → Fin n) → Fin m → Fin n :=
    fun ω => prog2 (attRows P eX eY eQ x w ω.1) ω.2 with hH₁
  set Rof : (Msg × Fin T → Fin κ → P.Rand × P.Ch) → Msg × Fin T → Fin κ → P.Rand :=
    fun u y i => (u y i).1 with hRof
  set f0 : (Msg × Fin T → Fin κ → P.Rand) → (Fin m → Fin n) → Fin c → Fin a := fun R h =>
    signTab S eQ eA (x, w) (hashOf eX eY h) R with hf0
  set E : (Msg × Fin T → Fin κ → P.Rand) → Finset (Fin c) := fun R =>
    Finset.univ.filter fun j => attCol P x w R (eQ.symm j) with hE
  have hsum : ∀ G : (Msg × Fin T → Fin κ → P.Rand × P.Ch) × (Fin m → Fin n) → ℝ≥0∞,
      ∑ u, NU * ∑ H, NH * G (u, H) = ∑ ω, NU * NH * G ω := by
    intro G
    rw [Fintype.sum_prod_type]
    simp only [Finset.mul_sum, mul_assoc]
  have hμ : ∑ _ω : (Msg × Fin T → Fin κ → P.Rand × P.Ch) × (Fin m → Fin n), NU * NH = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul,
      mul_mul_mul_comm, ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _),
      ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _), one_mul]
  have e0 : fsG0s (κ := κ) P recom eX eY eQ eA A x w = ∑ ω, NU * NH *
      prOutMRGen (recordGen (A.run x) (Gk (H₁ ω))) (H₁ ω) (f0 (Rof ω.1) (H₁ ω)) := by
    rw [← hsum]
    unfold fsG0s
    exact Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun H _ =>
      congrArg _ (prForge_eq_recordGen _ _ _ _ _ _ _ _ _))
  have e1 : fsG1 (κ := κ) P recom eX eY eQ eA A x w = ∑ ω, NU * NH *
      prOutMRGen (recordGen (A.run x) (Gk (H₁ ω))) (H₁ ω)
        (outTab P eQ eA (pairsOut P x w ω.1)) := by
    rw [← hsum]
    unfold fsG1
    exact Finset.sum_congr rfl fun u _ => congrArg _ (Finset.sum_congr rfl fun H _ =>
      congrArg _ (prWinProg_true_eq _ _ _ _ _ _ _ _))
  rw [e0, e1]
  refine rounds_upto_bad_local_dep (fun j => recordGen (A.run x) j) (fun ω => Gk (H₁ ω)) H₁
    (fun ω => f0 (Rof ω.1) (H₁ ω)) (fun ω => outTab P eQ eA (pairsOut P x w ω.1))
    (fun ω => E (Rof ω.1)) (fun _ => NU * NH) lam hμ.le ?_ ?_
  · intro ω j hj
    have hj' : ¬ attCol P x w (Rof ω.1) (eQ.symm j) := by simpa [hE] using hj
    exact outTab_eq_signTab P recom eX eY eQ eA x w ω.1 ω.2 j hj'
  · intro j y h₀ g
    set Φ : (Msg × Fin T → Fin κ → P.Rand) → (Fin m → Fin n) → ℝ≥0∞ := fun R h =>
      if Gk h = j ∧ h = h₀ ∧ ∀ y', y' ≠ y → f0 R h y' = g y' then 1 else 0 with hΦ
    set β : (Msg × Fin T → Fin κ → P.Rand) → ℝ≥0∞ := fun R =>
      if y ∈ E R then 1 else 0 with hβ
    have hL : ∑ ω, NU * NH * (if Gk (H₁ ω) = j ∧ H₁ ω = h₀ ∧
          ∀ y', y' ≠ y → f0 (Rof ω.1) (H₁ ω) y' = g y' then 1 else 0) *
          (if y ∈ E (Rof ω.1) then 1 else 0) =
        ∑ R, NR * ∑ h, NH * (Φ R h * β R) := by
      calc _ = ∑ ω, NU * NH * (Φ (Rof ω.1) (H₁ ω) * β (Rof ω.1)) :=
            Finset.sum_congr rfl fun ω _ => by ring
        _ = ∑ u, NU * ∑ H, NH * (Φ (Rof u) (H₁ (u, H)) * β (Rof u)) :=
            (hsum fun ω => Φ (Rof ω.1) (H₁ ω) * β (Rof ω.1)).symm
        _ = _ := sum_prog2_attRows_eq P eX eY eQ x w fun R h => Φ R h * β R
    have hR : ∑ ω, NU * NH * (if Gk (H₁ ω) = j ∧ H₁ ω = h₀ ∧
          ∀ y', y' ≠ y → f0 (Rof ω.1) (H₁ ω) y' = g y' then 1 else 0) =
        ∑ R, NR * ∑ h, NH * Φ R h := by
      calc _ = ∑ u, NU * ∑ H, NH * Φ (Rof u) (H₁ (u, H)) :=
            (hsum fun ω => Φ (Rof ω.1) (H₁ ω)).symm
        _ = _ := sum_prog2_attRows_eq P eX eY eQ x w Φ
    have hpt : ∀ h, ∑ R, Φ R h * β R ≤ lam * ∑ R, Φ R h := by
      intro h
      refine sum_mul_le_of_update (eQ.symm y) (fun R => Φ R h) β lam (fun R v => ?_)
        fun R => ?_
      · have hoff : ∀ y', y' ≠ y → f0 (Function.update R (eQ.symm y) v) h y' = f0 R h y' :=
          fun y' hy' => by
            simp [hf0, signTab, Function.update_of_ne (eQ.symm.injective.ne hy')]
        have hiff : (∀ y', y' ≠ y → f0 (Function.update R (eQ.symm y) v) h y' = g y') ↔
            (∀ y', y' ≠ y → f0 R h y' = g y') :=
          forall_congr' fun y' => imp_congr_right fun hy' => by rw [hoff y' hy']
        simp only [hΦ, hiff]
      · have h := sum_attCol_le P x w R (eQ.symm y)
        simpa [hβ, hE, hlam] using h
    rw [hL, hR]
    calc ∑ R, NR * ∑ h, NH * (Φ R h * β R) = NR * NH * ∑ h, ∑ R, Φ R h * β R := by
          simp only [Finset.mul_sum, mul_left_comm, mul_assoc]; rw [Finset.sum_comm]
      _ ≤ NR * NH * ∑ h, lam * ∑ R, Φ R h := by gcongr with h; exact hpt h
      _ = lam * ∑ R, NR * ∑ h, NH * Φ R h := by
          simp only [Finset.mul_sum, mul_left_comm, mul_assoc]; rw [Finset.sum_comm]

/-! ### The bad event: a forgery at an accepted point -/

omit [NeZero n] [NeZero c] in
/-- The oracle of G0* programmed at the attempt points of the pairs of the message `μ` only:
    summed over the pair coins and the oracle, a function of the prover randomness and of the
    programmed oracle has the sum it has at the unprogrammed oracle. -/
theorem sum_prog2_attRows_sel_eq (P : Sigma) (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (x : P.Stmt) (w : P.Wit) (μ : Msg)
    (F : (Msg × Fin T → Fin κ → P.Rand) → (Fin m → Fin n) → ℝ≥0∞) :
    ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch, ∑ H : Fin m → Fin n,
        F (fun y i => (u y i).1) (prog2 (fun j i => if (eQ.symm j).1 = μ then
          attRows P eX eY eQ x w u j i else none) H) =
      ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch, ∑ H : Fin m → Fin n,
        F (fun y i => (u y i).1) H := by
  rw [← (coinSplit P eY eQ).symm.sum_comp, ← (coinSplit P eY eQ).symm.sum_comp,
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun R _ => ?_
  have hR : ∀ c' : Fin c → Fin κ → Fin n,
      (fun y i => ((coinSplit P eY eQ).symm (R, c') y i).1) = R := fun _ => rfl
  have hrows : ∀ c' : Fin c → Fin κ → Fin n,
      (fun j i => if (eQ.symm j).1 = μ then
        attRows P eX eY eQ x w ((coinSplit P eY eQ).symm (R, c')) j i else none) =
      fun j i => if (eQ.symm j).1 = μ then
        some (eX ((eQ.symm j).1, P.commit x w (R (eQ.symm j) i)), c' j i) else none := by
    intro c'
    funext j i
    simp [attRows, coinSplit]
  simp only [hrows, hR]
  exact sum_prog2_sel_eq (fun j => (eQ.symm j).1 = μ) _ (F R)

omit [NeZero n] [NeZero c] in
/-- The prover randomness of attempt `i₀` of the pair `y₀` is independent of the oracle of G0*
    and of the coins of the pairs of the other messages: for a function `F` of the pair coins,
    reading only the pairs of messages other than `y₀.1`, and of the oracle, the average of
    `β r · F` is the product of the averages. -/
theorem sum_rand_mul_prog2_attRows_eq (P : Sigma) (eX : Msg × P.Com ≃ Fin m)
    (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) (x : P.Stmt) (w : P.Wit)
    (y₀ : Msg × Fin T) (i₀ : Fin κ) (β : P.Rand → ℝ≥0∞)
    (F : (Msg × Fin T → Fin κ → P.Rand × P.Ch) → (Fin m → Fin n) → ℝ≥0∞)
    (hF : ∀ u u' h, (∀ y, y.1 ≠ y₀.1 → u y = u' y) → F u h = F u' h) :
    ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
        (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ *
          ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
            (β (u y₀ i₀).1 * F u (prog2 (attRows P eX eY eQ x w u) H)) =
      (∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
        (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ * β (u y₀ i₀).1) *
        ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
          (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ *
            ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
              F u (prog2 (attRows P eX eY eQ x w u) H) := by
  set NU := (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ with hNU
  set NH := (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ with hNH
  have hdisj : ∀ (u : Msg × Fin T → Fin κ → P.Rand × P.Ch) (z : Fin m),
      (∀ j i, (eQ.symm j).1 = y₀.1 → matchAt z (attRows P eX eY eQ x w u j i) = none) ∨
      (∀ j i, ¬ (eQ.symm j).1 = y₀.1 → matchAt z (attRows P eX eY eQ x w u j i) = none) := by
    intro u z
    by_cases hz : (eX.symm z).1 = y₀.1
    · right
      intro j i hj
      simp only [attRows, matchAt, Option.bind_some, ite_eq_right_iff, reduceCtorEq, imp_false]
      intro he
      subst he
      rw [Equiv.symm_apply_apply] at hz
      exact hj hz
    · left
      intro j i hj
      simp only [attRows, matchAt, Option.bind_some, ite_eq_right_iff, reduceCtorEq, imp_false]
      intro he
      subst he
      rw [Equiv.symm_apply_apply] at hz
      exact hz hj
  have K : ∀ γ : (Msg × Fin T → Fin κ → P.Rand) → ℝ≥0∞,
      (∀ R R', (∀ y, y.1 = y₀.1 → R y = R' y) → γ R = γ R') →
      (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞) *
          ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch, ∑ H : Fin m → Fin n,
            γ (fun y i => (u y i).1) * F u (prog2 (attRows P eX eY eQ x w u) H) =
        (∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch, γ (fun y i => (u y i).1)) *
          ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch, ∑ H : Fin m → Fin n,
            F u (prog2 (fun j i => if (eQ.symm j).1 = y₀.1 then none else
              attRows P eX eY eQ x w u j i) H) := by
    intro γ hγ
    have hmerge := sum_sum_merge_eq (fun y : Msg × Fin T => y.1 = y₀.1)
      fun u : Msg × Fin T → Fin κ → P.Rand × P.Ch => ∑ H : Fin m → Fin n,
        γ (fun y i => (u y i).1) * F u (prog2 (attRows P eX eY eQ x w u) H)
    have hΦ : ∀ u₁ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
        (∑ H : Fin m → Fin n,
          γ (fun y i => ((fun y => if y.1 = y₀.1 then u₁ y else u y) y i).1) *
            F (fun y => if y.1 = y₀.1 then u₁ y else u y)
              (prog2 (attRows P eX eY eQ x w fun y => if y.1 = y₀.1 then u₁ y else u y) H)) =
        ∑ H : Fin m → Fin n, γ (fun y i => (u₁ y i).1) *
          F u (prog2 (fun j i => if (eQ.symm j).1 = y₀.1 then none else
            attRows P eX eY eQ x w u j i)
            (prog2 (fun j i => if (eQ.symm j).1 = y₀.1 then
              attRows P eX eY eQ x w u₁ j i else none) H)) := by
      intro u₁ u
      refine Finset.sum_congr rfl fun H _ => ?_
      rw [prog2_split _ (fun j => (eQ.symm j).1 = y₀.1) H (hdisj _)]
      rw [hγ _ (fun y i => (u₁ y i).1) fun y hy => by funext i; simp [hy],
        hF _ u _ fun y hy => by simp [hy]]
      congr 3
      · funext j i
        by_cases hj : (eQ.symm j).1 = y₀.1
        · simp [hj]
        · simp [hj, attRows]
      · grind [attRows]
    simp only [hΦ] at hmerge
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hmerge
    rw [← hmerge, Finset.sum_comm]
    rw [Finset.sum_mul]
    refine (Finset.sum_congr rfl fun u _ => sum_prog2_attRows_sel_eq P eX eY eQ x w y₀.1
      (fun R h => γ R * F u (prog2 (fun j i => if (eQ.symm j).1 = y₀.1 then none else
        attRows P eX eY eQ x w u j i) h))).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
  have K1 := K (fun R => β (R y₀ i₀)) fun R R' h => by rw [h y₀ rfl]
  have K2 := K (fun _ => 1) fun _ _ _ => rfl
  beta_reduce at K1 K2
  have hU0 : (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hUt : (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at K2
  rw [ENNReal.mul_right_inj hU0 hUt] at K2
  have hNU1 : NU * (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞) = 1 :=
    ENNReal.inv_mul_cancel hU0 hUt
  simp only [← Finset.mul_sum]
  calc NU * (NH * ∑ u, β (u y₀ i₀).1 * ∑ H, F u (prog2 (attRows P eX eY eQ x w u) H)) =
        NU * (NH * ∑ u, ∑ H, β (u y₀ i₀).1 * F u (prog2 (attRows P eX eY eQ x w u) H)) := by
        simp only [Finset.mul_sum]
    _ = NU * (NH * (NU * ((Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞) *
          ∑ u, ∑ H, β (u y₀ i₀).1 * F u (prog2 (attRows P eX eY eQ x w u) H)))) := by
        rw [← mul_assoc NU
          (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞), hNU1, one_mul]
    _ = _ := by rw [K1, K2]; ring

omit [NeZero n] [NeZero c] in
/-- Among the pair coins, the number whose attempt `i₀` of the pair `y₀` has the commitment
    `a₀` is at most `commitDistAt` times the number of all. -/
theorem sum_commit_pairCoins_le (P : Sigma) (x : P.Stmt) (w : P.Wit) (y₀ : Msg × Fin T)
    (i₀ : Fin κ) (a₀ : P.Com) :
    (∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
        if P.commit x w (u y₀ i₀).1 = a₀ then (1 : ℝ≥0∞) else 0) ≤
      P.commitDistAt x w * Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) := by
  have hp : (∑ p : P.Rand × P.Ch, if P.commit x w p.1 = a₀ then (1 : ℝ≥0∞) else 0) ≤
      P.commitDistAt x w * Fintype.card (P.Rand × P.Ch) := by
    rw [Fintype.sum_prod_type]
    calc ∑ r : P.Rand, ∑ _e : P.Ch, (if P.commit x w r = a₀ then (1 : ℝ≥0∞) else 0)
        = (Fintype.card P.Ch : ℝ≥0∞) * ∑ r : P.Rand, if P.commit x w r = a₀ then 1 else 0 := by
          rw [Finset.mul_sum]
          simp
      _ ≤ (Fintype.card P.Ch : ℝ≥0∞) * (P.commitDistAt x w * Fintype.card P.Rand) := by
          gcongr
          exact sum_rand_commit_le P x w a₀
      _ = P.commitDistAt x w * Fintype.card (P.Rand × P.Ch) := by
          rw [Fintype.card_prod, Nat.cast_mul]
          ring
  have hv : ∀ _u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
      (∑ v : Fin κ → P.Rand × P.Ch, if P.commit x w (v i₀).1 = a₀ then (1 : ℝ≥0∞) else 0) ≤
        P.commitDistAt x w * Fintype.card (Fin κ → P.Rand × P.Ch) := by
    intro _
    have h := sum_mul_le_of_update i₀ (fun _ => (1 : ℝ≥0∞))
      (fun v : Fin κ → P.Rand × P.Ch => if P.commit x w (v i₀).1 = a₀ then (1 : ℝ≥0∞) else 0)
      (P.commitDistAt x w) (fun _ _ => rfl) fun v => by
        simp only [Function.update_self]
        exact hp
    simpa using h
  have h := sum_mul_le_of_update y₀ (fun _ => (1 : ℝ≥0∞))
    (fun u : Msg × Fin T → Fin κ → P.Rand × P.Ch =>
      if P.commit x w (u y₀ i₀).1 = a₀ then (1 : ℝ≥0∞) else 0)
    (P.commitDistAt x w) (fun _ _ => rfl) fun u => by
      simp only [Function.update_self]
      exact hv u
  simpa using h

/-- The bad event of G1: the forgery point is an accepted point of a pair of the message of
    the forgery. Its probability is at most `T κ ε`, `ε = commitDistAt`: the test does not read
    the signing table at the pairs of that message (`prOutMRGen_recordGen_eq_prOutAvoidMRGen`,
    `prOutMRGen_congr_unread`), so the prover randomness of those pairs is independent of the
    rest of the run (`sum_rand_mul_prog2_attRows_eq`), and each of their `T κ` attempts has the
    forgery commitment with probability at most `ε`. -/
theorem fsG1_le_fsG1nb_add (P : Sigma) (recom : P.Stmt → P.Ch → P.Resp → P.Com)
    (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp)) (x : P.Stmt) (w : P.Wit) :
    fsG1 (κ := κ) P recom eX eY eQ eA A x w ≤
      fsG1nb (κ := κ) P recom eX eY eQ eA A x w + T * κ * P.commitDistAt x w := by
  set NU := (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞)⁻¹ with hNU
  set NH := (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ with hNH
  have hpt : ∀ (u : Msg × Fin T → Fin κ → P.Rand × P.Ch) (H : Fin m → Fin n),
      prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x (outTab P eQ eA (pairsOut P x w u))
          (prog2 (attRows P eX eY eQ x w u) H) (fun _ => true) =
        prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x (outTab P eQ eA (pairsOut P x w u))
          (prog2 (attRows P eX eY eQ x w u) H)
          (notAccFinal (κ := κ) P recom eX eY eQ A x (pairsOut P x w u)) +
        prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x (outTab P eQ eA (pairsOut P x w u))
          (prog2 (attRows P eX eY eQ x w u) H)
          (fun i => !notAccFinal (κ := κ) P recom eX eY eQ A x (pairsOut P x w u) i) := by
    intro u H
    unfold prWinProg
    simp only [Bool.and_true]
    exact prOut_withFinalB_add _ _ _ _
  have hbad : ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch, NU * ∑ H : Fin m → Fin n, NH *
      prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x (outTab P eQ eA (pairsOut P x w u))
        (prog2 (attRows P eX eY eQ x w u) H)
        (fun i => !notAccFinal (κ := κ) P recom eX eY eQ A x (pairsOut P x w u) i) ≤
      T * κ * P.commitDistAt x w := by
    have hU0 : (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hUt : (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.natCast_ne_top _
    have hNU1 : NU * (Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch) : ℝ≥0∞) = 1 :=
      ENNReal.inv_mul_cancel hU0 hUt
    have hlin : ∀ {ι : Type} (s : Finset ι)
        (Φ : ι → (Msg × Fin T → Fin κ → P.Rand × P.Ch) → (Fin m → Fin n) → ℝ≥0∞),
        ∑ u, NU * ∑ H, NH * ∑ t ∈ s, Φ t u H = ∑ t ∈ s, ∑ u, NU * ∑ H, NH * Φ t u H := by
      intro ι s Φ
      simp only [Finset.mul_sum]
      exact (Finset.sum_congr rfl fun u _ => Finset.sum_comm).trans Finset.sum_comm
    have hz : ∀ (f : Fin c → Fin a) (h : Fin m → Fin n) (b : Fin (m * n * ancW c k wd) → Bool),
        prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x f h b =
          ∑ z, prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x f h
            (fun i => b i && decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z)) := by
      intro f h b
      unfold prWinProg
      rw [prOut_withFinalB_eq_sum _ _ (forgePoint (fsAbortSig P κ Msg recom) eX A x)]
      simp only [Bool.and_assoc]
    have hbadpt : ∀ (u : Msg × Fin T → Fin κ → P.Rand × P.Ch) (H : Fin m → Fin n),
        prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x (outTab P eQ eA (pairsOut P x w u))
            (prog2 (attRows P eX eY eQ x w u) H)
            (fun i => !notAccFinal (κ := κ) P recom eX eY eQ A x (pairsOut P x w u) i) ≤
          ∑ z, (∑ τ : Fin T, ∑ i' : Fin κ,
            if P.commit x w (u ((eX.symm z).1, τ) i').1 = (eX.symm z).2 then 1 else 0) *
            prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x (outTab P eQ eA (pairsOut P x w u))
              (prog2 (attRows P eX eY eQ x w u) H)
              (fun i => decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z)) := by
      intro u H
      rw [hz]
      refine Finset.sum_le_sum fun z _ => ?_
      by_cases hE : ∃ j, (accRow P eX eY eQ (pairsOut P x w u) j).map Prod.fst = some z
      · have hb : (fun i => !notAccFinal (κ := κ) P recom eX eY eQ A x (pairsOut P x w u) i &&
            decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z)) =
            fun i => decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z) := by
          funext i
          by_cases hi : forgePoint (fsAbortSig P κ Msg recom) eX A x i = z
          · simp only [notAccFinal, hi, Bool.not_not, decide_true, Bool.and_true,
              decide_eq_true_eq]
            exact hE
          · simp [hi]
        rw [hb]
        obtain ⟨j, hj⟩ := hE
        have h1 : (1 : ℝ≥0∞) ≤ ∑ τ : Fin T, ∑ i' : Fin κ,
            if P.commit x w (u ((eX.symm z).1, τ) i').1 = (eX.symm z).2 then 1 else 0 := by
          cases ht : pairsOut P x w u (eQ.symm j) with
          | none => simp [accRow, ht] at hj
          | some t =>
            simp only [accRow, ht, Option.map_some, Option.some.injEq] at hj
            obtain ⟨i', hi'⟩ := exists_of_firstSome_eq_some _ t ht
            have hc : t.1 = P.commit x w (u (eQ.symm j) i').1 := by
              unfold fsAttempt at hi'
              split_ifs at hi'
              cases hi'
              rfl
            have hz' : eX.symm z = ((eQ.symm j).1, P.commit x w (u (eQ.symm j) i').1) := by
              rw [← hj, hc]
              simp
            refine le_trans ?_ (Finset.single_le_sum (fun _ _ => bot_le)
              (Finset.mem_univ (eQ.symm j).2))
            refine le_trans ?_ (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i'))
            simp [hz']
        calc _ = 1 * prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x
              (outTab P eQ eA (pairsOut P x w u)) (prog2 (attRows P eX eY eQ x w u) H)
              (fun i => decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z)) :=
              (one_mul _).symm
          _ ≤ _ := by gcongr
      · have hb : (fun i => !notAccFinal (κ := κ) P recom eX eY eQ A x (pairsOut P x w u) i &&
            decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z)) = fun _ => false := by
          funext i
          by_cases hi : forgePoint (fsAbortSig P κ Msg recom) eX A x i = z
          · simp only [notAccFinal, hi, Bool.not_not, decide_true, Bool.and_true,
              decide_eq_false_iff_not]
            exact hE
          · simp [hi]
        rw [hb]
        unfold prWinProg
        simp only [Bool.and_false, prOut_withFinalB_false]
        exact bot_le
    have hinv : ∀ (z : Fin m) (u u' : Msg × Fin T → Fin κ → P.Rand × P.Ch) (h : Fin m → Fin n),
        (∀ y, y.1 ≠ (eX.symm z).1 → u y = u' y) →
        prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x (outTab P eQ eA (pairsOut P x w u)) h
            (fun i => decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z)) =
          prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x (outTab P eQ eA (pairsOut P x w u')) h
            (fun i => decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z)) := by
      intro z u u' h hu
      have hG : ∀ i, (forgeTest (fsAbortSig P κ Msg recom) eY eQ A x i
          (h (forgePoint (fsAbortSig P κ Msg recom) eX A x i)) &&
          decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z)) = true →
          ∀ j, roundOutcomes m n c i j ∉
            Finset.univ.filter fun j' => (eQ.symm j').1 = (eX.symm z).1 := by
        intro i hi j hj
        simp only [Bool.and_eq_true, decide_eq_true_eq, forgeTest] at hi
        obtain ⟨⟨-, hro⟩, hfz⟩ := hi
        have hz' : (eX.symm z).1 = (A.forge i).1 := by
          rw [← hfz]
          simp [forgePoint, fsAbortSig]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact hro j (hj.trans hz')
      unfold prWinProg
      rw [prOut_withFinalB_toQAdv_eq, prOut_withFinalB_toQAdv_eq,
        prOutMRGen_recordGen_eq_prOutAvoidMRGen _ _ _ hG,
        prOutMRGen_recordGen_eq_prOutAvoidMRGen _ _ _ hG]
      refine prOutMRGen_congr_unread _ _ fun j hj => ?_
      have hj' : (eQ.symm j).1 ≠ (eX.symm z).1 := by simpa using hj
      simp only [outTab, pairsOut, hu _ hj']
    have hterm : ∀ (z : Fin m) (τ : Fin T) (i' : Fin κ),
        ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch, NU * ∑ H : Fin m → Fin n, NH *
          ((if P.commit x w (u ((eX.symm z).1, τ) i').1 = (eX.symm z).2 then 1 else 0) *
            prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x
              (outTab P eQ eA (pairsOut P x w u)) (prog2 (attRows P eX eY eQ x w u) H)
              (fun i => decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z))) ≤
        P.commitDistAt x w * ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch, NU *
          ∑ H : Fin m → Fin n, NH *
            prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x
              (outTab P eQ eA (pairsOut P x w u)) (prog2 (attRows P eX eY eQ x w u) H)
              (fun i => decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z)) := by
      intro z τ i'
      refine (le_of_eq (sum_rand_mul_prog2_attRows_eq P eX eY eQ x w ((eX.symm z).1, τ) i'
        (fun r => if P.commit x w r = (eX.symm z).2 then 1 else 0)
        (fun u h => prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x
          (outTab P eQ eA (pairsOut P x w u)) h
          (fun i => decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z)))
        fun u u' h hu => hinv z u u' h hu)).trans ?_
      gcongr
      rw [← Finset.mul_sum]
      calc NU * ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch,
            (if P.commit x w (u ((eX.symm z).1, τ) i').1 = (eX.symm z).2 then 1 else 0)
          ≤ NU * (P.commitDistAt x w *
              Fintype.card (Msg × Fin T → Fin κ → P.Rand × P.Ch)) := by
            gcongr
            exact sum_commit_pairCoins_le P x w _ i' _
        _ = P.commitDistAt x w := by rw [mul_left_comm, hNU1, mul_one]
    have hsumFz : ∀ (u : Msg × Fin T → Fin κ → P.Rand × P.Ch) (H : Fin m → Fin n),
        ∑ z, prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x
          (outTab P eQ eA (pairsOut P x w u)) (prog2 (attRows P eX eY eQ x w u) H)
          (fun i => decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z)) ≤ 1 := by
      intro u H
      have h := hz (outTab P eQ eA (pairsOut P x w u)) (prog2 (attRows P eX eY eQ x w u) H)
        fun _ => true
      simp only [Bool.true_and] at h
      rw [← h]
      exact prOut_le_one _ _
    have hE1 : ∑ _u : Msg × Fin T → Fin κ → P.Rand × P.Ch, NU *
        ∑ _H : Fin m → Fin n, NH * (1 : ℝ≥0∞) = 1 := by
      simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _), mul_one, ENNReal.mul_inv_cancel hU0 hUt]
    calc _ ≤ ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch, NU * ∑ H : Fin m → Fin n, NH *
          ∑ z, (∑ τ : Fin T, ∑ i' : Fin κ,
            if P.commit x w (u ((eX.symm z).1, τ) i').1 = (eX.symm z).2 then 1 else 0) *
            prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x (outTab P eQ eA (pairsOut P x w u))
              (prog2 (attRows P eX eY eQ x w u) H)
              (fun i => decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z)) := by
          gcongr with u _ H _
          exact hbadpt u H
      _ = ∑ z, ∑ τ : Fin T, ∑ i' : Fin κ,
          ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch, NU * ∑ H : Fin m → Fin n, NH *
            ((if P.commit x w (u ((eX.symm z).1, τ) i').1 = (eX.symm z).2 then 1 else 0) *
            prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x (outTab P eQ eA (pairsOut P x w u))
              (prog2 (attRows P eX eY eQ x w u) H)
              (fun i => decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z))) := by
          rw [hlin]
          refine Finset.sum_congr rfl fun z _ => ?_
          simp only [Finset.sum_mul]
          rw [hlin]
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [hlin]
      _ ≤ ∑ z, ∑ _τ : Fin T, ∑ _i' : Fin κ, P.commitDistAt x w *
          ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch, NU * ∑ H : Fin m → Fin n, NH *
            prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x (outTab P eQ eA (pairsOut P x w u))
              (prog2 (attRows P eX eY eQ x w u) H)
              (fun i => decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z)) := by
          gcongr with z _ τ _ i' _
          exact hterm z τ i'
      _ = T * κ * P.commitDistAt x w * ∑ z,
          ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch, NU * ∑ H : Fin m → Fin n, NH *
            prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x (outTab P eQ eA (pairsOut P x w u))
              (prog2 (attRows P eX eY eQ x w u) H)
              (fun i => decide (forgePoint (fsAbortSig P κ Msg recom) eX A x i = z)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ T * κ * P.commitDistAt x w * ∑ _u : Msg × Fin T → Fin κ → P.Rand × P.Ch, NU *
          ∑ _H : Fin m → Fin n, NH * (1 : ℝ≥0∞) := by
          rw [← hlin]
          gcongr with u _ H _
          exact hsumFz u H
      _ = T * κ * P.commitDistAt x w := by rw [hE1, mul_one]
  calc fsG1 (κ := κ) P recom eX eY eQ eA A x w =
        fsG1nb (κ := κ) P recom eX eY eQ eA A x w +
          ∑ u : Msg × Fin T → Fin κ → P.Rand × P.Ch, NU * ∑ H : Fin m → Fin n, NH *
            prWinProg (fsAbortSig P κ Msg recom) eX eY eQ A x
              (outTab P eQ eA (pairsOut P x w u)) (prog2 (attRows P eX eY eQ x w u) H)
              (fun i => !notAccFinal (κ := κ) P recom eX eY eQ A x (pairsOut P x w u) i) := by
        unfold fsG1 fsG1nb
        simp only [hpt, mul_add, Finset.sum_add_distrib]
        rfl
    _ ≤ _ := by gcongr

/-- The partial table of the programmed oracle of the outputs `o`: at a point, the value of the
    first accepted entry at it, nothing if there is none. Its `progOracle` is
    `prog1 (accRow P eX eY eQ o)`. -/
def accTab (P : Sigma) (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (o : Msg × Fin T → Option (P.Com × P.Ch × P.Resp)) : Fin m → Option (Fin n) :=
  fun z => firstSome fun j => matchAt z (accRow P eX eY eQ o j)

omit [Fintype Msg] [DecidableEq Msg] [NeZero n] [NeZero c] in
/-- At a point that is not an accepted point, the table of the programmed oracle is undefined. -/
theorem accTab_eq_none (P : Sigma) (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (o : Msg × Fin T → Option (P.Com × P.Ch × P.Resp)) (z : Fin m)
    (h : ¬ ∃ j, (accRow P eX eY eQ o j).map Prod.fst = some z) :
    accTab P eX eY eQ o z = none := by
  refine firstSome_eq_none _ fun j => ?_
  push Not at h
  have hj := h j
  unfold matchAt
  cases hd : accRow P eX eY eQ o j with
  | none => rfl
  | some e =>
    rw [hd] at hj
    have he : e.1 ≠ z := fun he => hj (by simp [he])
    simp [he]

/-- The no-message adversary of G3 at the statement `x` and the simulator coins `s`: the
    adversary `A` with the rounds answered by the signing table of the simulated outputs, its
    queries routed (`routeAdv`) so that it sees the oracle programmed at the accepted simulated
    points while it queries `H` only, and the forgery of `A` output when its point is not an
    accepted point and its message is not a round outcome. Its cost: `flatQ q k q` queries to
    `H`, one per query of the flattened `A`; the `κ` simulated attempts of each of the
    `|Msg| T` pairs; and around each query one router permutation and one addition of a
    programmed value on its register. -/
def fsNMA [NeZero m] (P : Sigma) (recom : P.Stmt → P.Ch → P.Resp → P.Com)
    (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp)) (x : P.Stmt)
    (s : Msg × Fin T → Fin κ → P.SimRand × P.Ch) :
    QNMAAdv m n (ancW c k wd * (2 * (m * n))) (flatQ q k q) Msg (P.Ch × P.Resp) where
  adv := routeAdv (toQAdv (A.run x) (outTab P eQ eA fun y => pairSimOut P x (s y)))
    (accTab P eX eY eQ fun y => pairSimOut P x (s y))
  forge i :=
    if notAccFinal (κ := κ) P recom eX eY eQ A x (fun y => pairSimOut P x (s y))
        (routeBase (accTab P eX eY eQ fun y => pairSimOut P x (s y)) i) &&
      decide (∀ r, (eQ.symm (roundOutcomes m n c
        (routeBase (accTab P eX eY eQ fun y => pairSimOut P x (s y)) i) r)).1 ≠
          (A.forge (routeBase (accTab P eX eY eQ fun y => pairSimOut P x (s y)) i)).1)
    then some (A.forge (routeBase (accTab P eX eY eQ fun y => pairSimOut P x (s y)) i))
    else none

/-- G3 is the no-message advantage of `fsNMA`: at the forgeries outside the accepted points the
    programmed oracle is `H`, and the routed adversary sees the programmed oracle
    (`prOut_routeAdv`). -/
theorem fsG3_eq_qNMAProgAdvantage [NeZero m] (P : Sigma)
    (recom : P.Stmt → P.Ch → P.Resp → P.Com)
    (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp)) (x : P.Stmt) :
    fsG3 (κ := κ) P recom eX eY eQ eA A x =
      qNMAProgAdvantage (fsAbortSig P κ Msg recom) eX eY x
        (fsNMA (κ := κ) P recom eX eY eQ eA A x) := by
  unfold fsG3 qNMAProgAdvantage prNMA fsProgWin
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun H _ => ?_
  congr 1
  unfold prWinProg
  set o : Msg × Fin T → Option (P.Com × P.Ch × P.Resp) := fun y => pairSimOut P x (s y) with ho
  change prOut _ (progOracle (accTab P eX eY eQ o) H) = _
  rw [← prOut_routeAdv, ← routeAdv_withFinalB]
  congr 2
  funext i
  set S := fsAbortSig P κ Msg recom with hS
  set j := routeBase (accTab P eX eY eQ o) i with hj
  have hf : (fsNMA (κ := κ) P recom eX eY eQ eA A x s).forge i =
      if notAccFinal (κ := κ) P recom eX eY eQ A x o j &&
        decide (∀ r, (eQ.symm (roundOutcomes m n c j r)).1 ≠ (A.forge j).1)
      then some (A.forge j) else none := rfl
  unfold nmaTest
  rw [hf]
  cases hn : notAccFinal (κ := κ) P recom eX eY eQ A x o j
  · simp
  · have hp : prog1 (accRow P eX eY eQ o) H (forgePoint S eX A x j) =
        H (forgePoint S eX A x j) := by
      change (accTab P eX eY eQ o (forgePoint S eX A x j)).getD _ = _
      rw [accTab_eq_none]
      · rfl
      · simpa [notAccFinal] using hn
    rw [hp]
    by_cases hd : ∀ r, (eQ.symm (roundOutcomes m n c j r)).1 ≠ (A.forge j).1 <;>
      simp [hd, forgeTest, QROMSig.verifyH, hashOf, forgePoint]

/-- CMA to NMA for Fiat–Shamir with aborts at the key `(x, w)` with zero HVZK distance: the
    winning probability of `A` is at most the no-message advantage of `fsNMA` plus the hops
    G0* → G1 (`k T κ² ε`), the bad event of G1 (`T κ ε`) and G1 → G2
    (`2 (flatQ q k q + 1) √(T κ (ρ ⊔ ε))`), the sum capped at `1`. -/
theorem fsAborts_qcma_to_nma_at [NeZero m] (P : Sigma)
    (recom : P.Stmt → P.Ch → P.Resp → P.Com)
    (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp)) {x : P.Stmt} {w : P.Wit}
    (hzk : P.hvzkDistAt x w = 0) :
    ∑ R : Msg × Fin T → Fin κ → P.Rand,
        (Fintype.card (Msg × Fin T → Fin κ → P.Rand) : ℝ≥0∞)⁻¹ *
          ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
            prForge (fsAbortSig P κ Msg recom) eX eY eQ eA A (x, (x, w)) H R ≤
      qNMAProgAdvantage (fsAbortSig P κ Msg recom) eX eY x
          (fsNMA (κ := κ) P recom eX eY eQ eA A x) +
        min 1 (k * (T * κ ^ 2 * P.commitDistAt x w) + T * κ * P.commitDistAt x w +
          2 * ((flatQ q k q + 1 : ℕ) : ℝ≥0∞) *
            ((T : ℝ≥0∞) * (κ * (P.rejCommitDistAt x w ⊔ P.commitDistAt x w))) ^ (1 / 2 : ℝ)) := by
  have h1 := CatCrypt.Crypto.le_add_of_absDiff_le
    (fsG0s_fsG1_le (κ := κ) P recom eX eY eQ eA A x w)
  have h2 := fsG1_le_fsG1nb_add (κ := κ) P recom eX eY eQ eA A x w
  have h3 := CatCrypt.Crypto.le_add_of_absDiff_le
    (fsG1nb_fsG2_le (κ := κ) P recom eX eY eQ eA A x w)
  rw [fsG2_eq_fsG3 hzk, fsG3_eq_qNMAProgAdvantage] at h3
  have hle : ∑ R : Msg × Fin T → Fin κ → P.Rand,
        (Fintype.card (Msg × Fin T → Fin κ → P.Rand) : ℝ≥0∞)⁻¹ *
          ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
            prForge (fsAbortSig P κ Msg recom) eX eY eQ eA A (x, (x, w)) H R ≤ 1 := by
    calc _ ≤ ∑ R : Msg × Fin T → Fin κ → P.Rand,
          (Fintype.card (Msg × Fin T → Fin κ → P.Rand) : ℝ≥0∞)⁻¹ *
            ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ * 1 := by
          gcongr with R _ H _
          exact prForge_le_one _ _ _ _ _ _ _ _ _
      _ = 1 := by
          simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (by simp),
            mul_one, ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (by simp)]
  rw [fsG0_eq_fsG0s] at hle ⊢
  rcases le_total 1 (k * (T * κ ^ 2 * P.commitDistAt x w) + T * κ * P.commitDistAt x w +
      2 * ((flatQ q k q + 1 : ℕ) : ℝ≥0∞) *
        ((T : ℝ≥0∞) * (κ * (P.rejCommitDistAt x w ⊔ P.commitDistAt x w))) ^ (1 / 2 : ℝ)) with
    h | h
  · rw [min_eq_left h]
    exact hle.trans le_add_self
  · rw [min_eq_right h]
    exact (h1.trans (add_le_add (h2.trans (add_le_add h3 le_rfl)) le_rfl)).trans_eq (by ring)

/-- CMA to NMA for Fiat–Shamir with aborts with exact simulation, in the quantum random-oracle
    model: the quantum EUF-CMA advantage of `A` is at most the average over the keys of the
    no-message advantage of `fsNMA` at the public key plus the per-key terms of
    `fsAborts_qcma_to_nma_at`, capped at `1`. -/
theorem fsAborts_qcma_to_nma [NeZero m] (P : Sigma) [Fintype P.Stmt] [Fintype P.Wit]
    (recom : P.Stmt → P.Ch → P.Resp → P.Com)
    (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (P.Ch × P.Resp) ≃ Fin a)
    (A : QSigAdv m n wd q k c a T Msg P.Stmt (P.Ch × P.Resp))
    (hzk : ∀ xw ∈ P.gen.support, P.hvzkDistAt xw.1 xw.2 = 0) :
    qEUFCMAAdvantage (fsAbortSig P κ Msg recom) eX eY eQ eA A ≤
      ∑ ks, (fsAbortSig P κ Msg recom).keygen ks *
        (qNMAProgAdvantage (fsAbortSig P κ Msg recom) eX eY ks.1
            (fsNMA (κ := κ) P recom eX eY eQ eA A ks.1) +
          min 1 (k * (T * κ ^ 2 * P.commitDistAt ks.2.1 ks.2.2) +
            T * κ * P.commitDistAt ks.2.1 ks.2.2 +
            2 * ((flatQ q k q + 1 : ℕ) : ℝ≥0∞) *
              ((T : ℝ≥0∞) * (κ * (P.rejCommitDistAt ks.2.1 ks.2.2 ⊔
                P.commitDistAt ks.2.1 ks.2.2))) ^ (1 / 2 : ℝ))) := by
  unfold qEUFCMAAdvantage
  refine Finset.sum_le_sum fun ks _ => ?_
  by_cases h0 : (fsAbortSig P κ Msg recom).keygen ks = 0
  · simp [h0]
  · obtain ⟨xw, hxw, rfl⟩ : ∃ xw ∈ P.gen.support, (xw.1, xw) = ks :=
      (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr h0)
    gcongr
    exact fsAborts_qcma_to_nma_at P recom eX eY eQ eA A (hzk xw hxw)

end Games

end CatCrypt.Quantum.QROM
