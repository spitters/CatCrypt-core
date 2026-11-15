/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.FSAborts
public import CatCryptCore.Quantum.QROM.QSearch

/-!
# Fiat–Shamir with aborts at a lossy key

The terminal steps of the QROM security of Fiat–Shamir with aborts.

At a lossy statement `x`, every commitment `a` has few challenges `e` with an accepted
response (`#{e | ∃ z, verify x a e z} ≤ ε_ls · |Ch|`). A no-message adversary that forges
for `fsAbortSig` at `x` is then a Fiat–Shamir prover (`prOut_withFinalB_eq_sum_prOutAt`,
`moveAdv`) whose verifier projector at each commitment is nonzero for at most
`ε_ls · |Ch|` challenges, and the measure-and-reprogram bound of Don, Fehr, Majenz and
Schaffner (`fiatShamir_random_oracle`) with `sum_prInt_le_card_div` bounds its advantage by
`(2q + 1)² ε_ls`.

The lossy-key hop replaces the real statement distribution by the lossy one. The reduction
`B_lossyQ` has no oracle access: it draws the coefficients of a polynomial of degree
`< K` over the field of `PolyData`, runs the no-message adversary against the polynomial
table and checks the forgery itself. For `K ≥ 2 (q + 1)` its acceptance probability at
every statement is the no-message advantage (`qStdAcc_B_lossyQ`), by the `K`-wise
independence of the table (`KWiseInvariant.push`), since the run with the forgery test
reads at most `2 (q + 1)` points of the oracle.

## Main definitions

* `nmaPoint`, `nmaCheck` — the point at which the no-message test reads the oracle and the
  test of the value read there
* `B_lossyQ` — the distinguisher without oracle access of the lossy-key hop

## Main results

* `sum_prInt_le_card_div` — if every commitment has at most `s` challenges with a nonzero
  verifier projector, `∑ x, prInt A V H x ≤ s / n`
* `fsAborts_nma_le_lossy` — at a lossy statement the no-message advantage is at most
  `(2q + 1)² ε_ls`
* `fsAborts_nma_lossy_avg_le` — the same bound averaged over a lossy statement distribution
* `qStdAcc_B_lossyQ` — the acceptance probability of `B_lossyQ` is the no-message advantage
* `fsAborts_nma_lossy_hop_le` — the no-message advantage at the real statement
  distribution is at most `qDistAdv` of `B_lossyQ` plus `(2q + 1)² ε_ls`

## References

* [Don, Fehr, Majenz, Schaffner — Security of the Fiat-Shamir Transformation in the Quantum
  Random-Oracle Model, CRYPTO 2019], Theorem 2
* [Zhandry — Secure Identity-Based Encryption in the Quantum Random Oracle Model,
  CRYPTO 2012], Theorem 6.1
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal

noncomputable section

namespace CatCrypt.Quantum.QROM

open CatCrypt.Quantum CatCrypt.Prob CatCrypt.Crypto.FiatShamirROM

/-! ## Verifiers with few accepting challenges per commitment -/

section CardDiv

variable {m n w q : ℕ} [NeZero n]

/-- If every commitment `x` has at most `s` challenges with a nonzero verifier projector,
    the interactive simulator succeeds with probability at most `s / n`. -/
theorem sum_prInt_le_card_div (A : QAdv m n w q) (V : QVerifier m n w) (H : Fin m → Fin n)
    (s : ℕ) (hV : ∀ x, (Finset.univ.filter fun θ => V.proj x θ ≠ 0).card ≤ s) :
    ∑ x, prInt A V H x ≤ (s : ℝ≥0∞) / n := by
  classical
  have hemb : ∀ x, ∃ g : Fin s → Fin n, ∀ θ, V.proj x θ ≠ 0 → θ ∈ Set.range g := by
    intro x
    set S := Finset.univ.filter fun θ => V.proj x θ ≠ 0 with hS
    refine ⟨fun i => if h : i.1 < S.card then S.equivFin.symm ⟨i.1, h⟩ else 0, fun θ hθ => ?_⟩
    have hmem : θ ∈ S := by simp [hS, hθ]
    refine ⟨⟨(S.equivFin ⟨θ, hmem⟩).1, lt_of_lt_of_le (S.equivFin ⟨θ, hmem⟩).2 (hV x)⟩, ?_⟩
    simp
  choose c hc using hemb
  set N : ℝ≥0∞ := ((2 * q + 1 : ℕ) : ℝ≥0∞) with hN
  have hN0 : N ≠ 0 := Nat.cast_ne_zero.mpr (2 * q).succ_ne_zero
  have hNt : N ≠ ⊤ := ENNReal.natCast_ne_top _
  set f : Fin m → Fin s → Option (Fin q × Bool) → ℝ≥0∞ :=
    fun x i t => prSimAcc (A.withVerifier V x (c x i)) H (c x i) x t with hf
  have hat : ∀ x t, prIntAt A V H x t ≤ (n : ℝ≥0∞)⁻¹ * ∑ i, f x i t := by
    intro x t
    unfold prIntAt
    gcongr
    calc ∑ θ, prSimAcc (A.withVerifier V x θ) H θ x t
        = ∑ θ ∈ Finset.univ.image (c x), prSimAcc (A.withVerifier V x θ) H θ x t := by
          refine (Finset.sum_subset (Finset.subset_univ _) fun θ _ hθ => ?_).symm
          refine prSimAcc_eq_zero _ H θ x t ?_
          by_contra h
          obtain ⟨i, hi⟩ := hc x θ h
          exact hθ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
      _ ≤ ∑ i, f x i t := Finset.sum_image_le_of_nonneg fun _ _ => zero_le
  have ht : ∀ t i, ∑ x, f x i t ≤ 1 := fun t i =>
    (Finset.sum_le_sum fun x _ => (prSimAcc_le _ H (c x i) x t).trans_eq
      (by rw [simChain_branch_eq_fsChain (c := fun x => c x i)]; rfl)).trans
      (sum_fsChain_trace_le_one A H (fun x => c x i) t)
  calc ∑ x, prInt A V H x
      = N⁻¹ * ∑ t, ∑ x, prIntAt A V H x t := by
        simp only [prInt, ← Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ N⁻¹ * ∑ t, ∑ x, (n : ℝ≥0∞)⁻¹ * ∑ i, f x i t := by
        gcongr with t _ x
        exact hat x t
    _ = N⁻¹ * ∑ t, (n : ℝ≥0∞)⁻¹ * ∑ i, ∑ x, f x i t := by
        simp only [← Finset.mul_sum]
        congr 1
        congr 1
        exact Finset.sum_congr rfl fun t _ => Finset.sum_comm
    _ ≤ N⁻¹ * ∑ _t : Option (Fin q × Bool), (n : ℝ≥0∞)⁻¹ * ∑ _i : Fin s, 1 := by
        gcongr with t _ i
        exact ht t i
    _ = (s : ℝ≥0∞) / n := by
        rw [Finset.sum_const, Finset.card_univ, card_mrIndex, nsmul_eq_mul, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← hN, ← mul_assoc,
          ENNReal.inv_mul_cancel hN0 hNt, one_mul, ENNReal.div_eq_inv_mul]

end CardDiv

/-! ## The no-message test as a test of the oracle at one point -/

section Point

variable {m n w q : ℕ} {Msg PK SK Sig X Y : Type}

/-- The point at which the no-message test of the basis state `i` reads the oracle: the
    verification point of its forgery, `0` for no forgery. -/
def nmaPoint [NeZero m] (S : QROMSig Msg PK SK Sig X Y) (eX : X ≃ Fin m) (pk : PK)
    (B : QNMAAdv m n w q Msg Sig) (i : Fin (m * n * w)) : Fin m :=
  (B.forge i).elim 0 fun f => eX (S.point pk f.1 f.2)

/-- The no-message test of the basis state `i` at the encoded hash value `θ` at its
    verification point. -/
def nmaCheck (S : QROMSig Msg PK SK Sig X Y) (eY : Y ≃ Fin n) (pk : PK)
    (B : QNMAAdv m n w q Msg Sig) (i : Fin (m * n * w)) (θ : Fin n) : Bool :=
  (B.forge i).elim false fun f => S.check pk f.1 f.2 (eY.symm θ)

/-- The no-message test reads the oracle at `nmaPoint` and tests the value with
    `nmaCheck`. -/
theorem nmaTest_eq [NeZero m] (S : QROMSig Msg PK SK Sig X Y) (eX : X ≃ Fin m)
    (eY : Y ≃ Fin n) (pk : PK) (B : QNMAAdv m n w q Msg Sig) (H : Fin m → Fin n) :
    nmaTest S eX eY pk B H = fun i => nmaCheck S eY pk B i (H (nmaPoint S eX pk B i)) := by
  funext i
  unfold nmaTest nmaCheck nmaPoint
  cases B.forge i <;> rfl

end Point

/-! ## The no-message advantage at a lossy statement -/

section Lossy

variable {m n w q κ : ℕ} {Msg : Type} [NeZero m] [NeZero n]

open Classical in
/-- At a lossy statement `x`, at which every commitment has at most `ε_ls · |Ch|` challenges
    with an accepted response, a no-message adversary with `q` queries forges for
    Fiat–Shamir with aborts with probability at most `(2q + 1)² ε_ls`. -/
theorem fsAborts_nma_le_lossy {Ω : Type} [Fintype Ω] (P : Sigma)
    (recom : P.Stmt → P.Ch → P.Resp → P.Com) (x : P.Stmt) (ε_ls : ℝ≥0∞)
    (hls : ∀ a, ((Finset.univ.filter fun e : P.Ch => ∃ z, P.verify x a e z = true).card :
      ℝ≥0∞) ≤ ε_ls * Fintype.card P.Ch)
    (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n)
    (B : Ω → QNMAAdv m n w q Msg (P.Ch × P.Resp)) :
    qNMAProgAdvantage (fsAbortSig P κ Msg recom) eX eY x B ≤
      ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 * ε_ls := by
  set S := fsAbortSig P κ Msg recom with hSdef
  set c : ℝ≥0∞ := ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 * ε_ls with hc
  have hn : Fintype.card P.Ch = n := by rw [Fintype.card_congr eY, Fintype.card_fin]
  have hω : ∀ B' : QNMAAdv m n w q Msg (P.Ch × P.Resp), prNMA S eX eY x B' ≤ c := by
    intro B'
    set p := nmaPoint S eX x B' with hp
    set g := nmaCheck S eY x B' with hg
    set V : QVerifier m n (w * m) := QVerifier.ofPred (moveAcc p g) with hV
    set A' := moveAdv B'.adv p with hA'
    have hcount : ∀ x', (Finset.univ.filter fun θ => V.proj x' θ ≠ 0).card ≤
        (Finset.univ.filter fun e : P.Ch => ∃ z, P.verify x (eX.symm x').2 e z = true).card := by
      intro x'
      refine (Finset.card_le_card fun θ hθ => ?_).trans (Finset.card_image_le (f := eY))
      have h1 : V.proj x' θ ≠ 0 := (Finset.mem_filter.mp hθ).2
      have key : ∀ k, x' = p k → g k θ = true → θ ∈ Finset.image eY
          (Finset.univ.filter fun e : P.Ch => ∃ z, P.verify x (eX.symm x').2 e z = true) := by
        intro k hxk hgk
        rw [hg] at hgk
        rw [hp] at hxk
        unfold nmaCheck at hgk
        unfold nmaPoint at hxk
        cases hf : B'.forge k with
        | none => simp [hf] at hgk
        | some f =>
          obtain ⟨μ, e, z⟩ := f
          simp only [hf, Option.elim, hSdef, fsAbortSig, Bool.and_eq_true,
            decide_eq_true_eq] at hgk hxk
          obtain ⟨he, hv⟩ := hgk
          refine Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, z, ?_⟩, ?_⟩
          · rw [hxk, Equiv.symm_apply_apply]
            exact hv
          · rw [← he, Equiv.apply_symm_apply]
      obtain ⟨j, hj⟩ : ∃ j, moveAcc p g x' θ j = true := by
        by_contra hne
        push Not at hne
        exact h1 (diagB_eq_zero (by simpa using hne))
      simp only [moveAcc, Bool.and_eq_true, decide_eq_true_eq] at hj
      exact key _ hj.1 hj.2
    set s := Finset.univ.sup fun x' => (Finset.univ.filter fun θ => V.proj x' θ ≠ 0).card
      with hsdef
    have hs : (s : ℝ≥0∞) / n ≤ ε_ls := by
      obtain ⟨x₀, -, hx₀⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin m))
        Finset.univ_nonempty fun x' => (Finset.univ.filter fun θ => V.proj x' θ ≠ 0).card
      refine ENNReal.div_le_of_le_mul ?_
      rw [← hsdef] at hx₀
      rw [hx₀]
      exact (Nat.cast_le.mpr (hcount x₀)).trans ((hls _).trans_eq (by rw [hn]))
    have hprog : ∀ H, prOut (B'.adv.withFinalB (nmaTest S eX eY x B' H)) H =
        ∑ x', prOutAt (A'.withVerifier V x' (H x')) H x' := by
      intro H
      rw [nmaTest_eq]
      exact prOut_withFinalB_eq_sum_prOutAt _ _ _ H
    have hcard0 : (Fintype.card (Fin m → Fin n) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    calc prNMA S eX eY x B'
        = (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
            ∑ H : Fin m → Fin n, ∑ x', prOutAt (A'.withVerifier V x' (H x')) H x' := by
          simp only [prNMA, hprog, Finset.mul_sum]
      _ ≤ ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 *
            ((Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
              ∑ H : Fin m → Fin n, ∑ x', prInt A' V H x') := fiatShamir_random_oracle A' V
      _ ≤ ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 *
            ((Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
              ∑ _H : Fin m → Fin n, (s : ℝ≥0∞) / n) := by
          gcongr with H
          exact sum_prInt_le_card_div A' V H s fun x' =>
            Finset.le_sup (f := fun x' => (Finset.univ.filter fun θ => V.proj x' θ ≠ 0).card)
              (Finset.mem_univ x')
      _ = ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 * ((s : ℝ≥0∞) / n) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc
            ((Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹),
            ENNReal.inv_mul_cancel hcard0 (ENNReal.natCast_ne_top _), one_mul]
      _ ≤ c := mul_le_mul_right hs _
  unfold qNMAProgAdvantage
  calc ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * prNMA S eX eY x (B ω)
      ≤ ∑ _ω : Ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * c := by
        gcongr with ω
        exact hω (B ω)
    _ ≤ c := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
        exact mul_le_of_le_one_left zero_le (ENNReal.mul_inv_le_one _)

open Classical in
/-- The bound of `fsAborts_nma_le_lossy` averaged over a statement distribution `D₁` whose
    support consists of lossy statements. -/
theorem fsAborts_nma_lossy_avg_le {Ω : Type} [Fintype Ω] (P : Sigma)
    (recom : P.Stmt → P.Ch → P.Resp → P.Com) (D₁ : SDistr P.Stmt) (ε_ls : ℝ≥0∞)
    (hls : ∀ x, D₁ (some x) ≠ 0 → ∀ a,
      ((Finset.univ.filter fun e : P.Ch => ∃ z, P.verify x a e z = true).card : ℝ≥0∞) ≤
        ε_ls * Fintype.card P.Ch)
    (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n)
    (B : Ω → QNMAAdv m n w q Msg (P.Ch × P.Resp)) :
    sdExp D₁ (fun x => qNMAProgAdvantage (fsAbortSig P κ Msg recom) eX eY x B) ≤
      ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 * ε_ls := by
  set c : ℝ≥0∞ := ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 * ε_ls with hc
  unfold sdExp
  calc ∑' x, D₁ (some x) * qNMAProgAdvantage (fsAbortSig P κ Msg recom) eX eY x B
      ≤ ∑' x, D₁ (some x) * c := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases h : D₁ (some x) = 0
        · simp [h]
        · exact mul_le_mul_right (fsAborts_nma_le_lossy P recom x ε_ls (hls x h) eX eY B) _
    _ = (∑' x, D₁ (some x)) * c := ENNReal.tsum_mul_right
    _ ≤ 1 * c := by
        gcongr
        exact (ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective _) _).trans_eq
          D₁.tsum_coe
    _ = c := one_mul _

end Lossy

/-! ## The lossy-key hop -/

section Hop

variable {m n w q κ : ℕ} {Msg PK SK Sig X Y : Type} [NeZero m] [NeZero n]

/-- The run of a no-message adversary with its forgery test, as a function of the oracle, is
    invariant under every `K`-wise independent weight for `K ≥ 2 (q + 1)`: with the test as
    one more query it reads at most `2 (q + 1)` points. -/
theorem kWiseInvariant_prOut_nmaTest (S : QROMSig Msg PK SK Sig X Y) (eX : X ≃ Fin m)
    (eY : Y ≃ Fin n) (pk : PK) (B : QNMAAdv m n w q Msg Sig) {K : ℕ} (hK : 2 * (q + 1) ≤ K) :
    KWiseInvariant K (fun H => prOut (B.adv.withFinalB (nmaTest S eX eY pk B H)) H) := by
  have e : (fun H => prOut (B.adv.withFinalB (nmaTest S eX eY pk B H)) H) = fun H =>
      ENNReal.ofReal (prOutC (finalQAdv B.adv (nmaPoint S eX pk B) (nmaCheck S eY pk B)) H).re :=
    funext fun H => by
      rw [nmaTest_eq, prOut_withFinalB_eq_prOut_finalQAdv, prOut_eq_ofReal_re]
  rw [e]
  exact (KWiseInvariant.of_dependsOn (prOutC_dependsOn _) fun H => prOutC_re_nonneg _ _).mono hK

/-- The distinguisher of the lossy-key hop: on the public key `pk` and the coins `(ω, cf)`,
    the no-message adversary `B ω` run against the table of the polynomial with coefficients
    `cf` of degree `< K`, followed by the projector onto the basis states whose forgery
    verifies under that table. It has no oracle access. -/
def B_lossyQ (S : QROMSig Msg PK SK Sig X Y) (eX : X ≃ Fin m) (eY : Y ≃ Fin n)
    (PD : PolyData (Fin m) (Fin n)) (K : ℕ) {Ω : Type} (B : Ω → QNMAAdv m n w q Msg Sig) :
    QStdDist (Ω × (Fin K → PD.F)) PK m n w :=
  fun pk c => absorbOracle ((B c.1).adv.withFinalB
    (nmaTest S eX eY pk (B c.1) (PD.table K c.2))) (PD.table K c.2)

/-- For `K ≥ 2 (q + 1)` the acceptance probability of `B_lossyQ` at the public key `pk` is the
    no-message advantage at `pk`. -/
theorem qStdAcc_B_lossyQ {Ω : Type} [Fintype Ω] (S : QROMSig Msg PK SK Sig X Y)
    (eX : X ≃ Fin m) (eY : Y ≃ Fin n) (PD : PolyData (Fin m) (Fin n)) {K : ℕ}
    (hK : 2 * (q + 1) ≤ K) (B : Ω → QNMAAdv m n w q Msg Sig) (pk : PK) :
    qStdAcc (B_lossyQ S eX eY PD K B) pk = qNMAProgAdvantage S eX eY pk B := by
  unfold qStdAcc B_lossyQ qNMAProgAdvantage prNMA prOut0
  simp only [prOut_absorbOracle]
  rw [sum_prod_uniform]
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 1
  exact (kWiseInvariant_prOut_nmaTest S eX eY pk (B ω) hK).push (PD.table K) (PD.kWise K)

open Classical in
/-- The lossy-key hop with the terminal bound: at the real statement distribution `D₀` the
    no-message advantage against Fiat–Shamir with aborts is at most the advantage of
    `B_lossyQ` in distinguishing `D₀` from a lossy statement distribution `D₁`, plus
    `(2q + 1)² ε_ls`. -/
theorem fsAborts_nma_lossy_hop_le {Ω : Type} [Fintype Ω] (P : Sigma)
    (recom : P.Stmt → P.Ch → P.Resp → P.Com) (D₀ D₁ : SDistr P.Stmt) (ε_ls : ℝ≥0∞)
    (hls : ∀ x, D₁ (some x) ≠ 0 → ∀ a,
      ((Finset.univ.filter fun e : P.Ch => ∃ z, P.verify x a e z = true).card : ℝ≥0∞) ≤
        ε_ls * Fintype.card P.Ch)
    (eX : Msg × P.Com ≃ Fin m) (eY : P.Ch ≃ Fin n) (PD : PolyData (Fin m) (Fin n)) {K : ℕ}
    (hK : 2 * (q + 1) ≤ K) (B : Ω → QNMAAdv m n w q Msg (P.Ch × P.Resp)) :
    sdExp D₀ (fun x => qNMAProgAdvantage (fsAbortSig P κ Msg recom) eX eY x B) ≤
      qDistAdv D₀ D₁ (B_lossyQ (fsAbortSig P κ Msg recom) eX eY PD K B) +
        ((2 * q + 1 : ℕ) : ℝ≥0∞) ^ 2 * ε_ls := by
  have hE : qStdAcc (B_lossyQ (fsAbortSig P κ Msg recom) eX eY PD K B) =
      fun x => qNMAProgAdvantage (fsAbortSig P κ Msg recom) eX eY x B :=
    funext (qStdAcc_B_lossyQ _ eX eY PD hK B)
  have h := (absDiff_le_iff.mp (le_refl (qDistAdv D₀ D₁
    (B_lossyQ (fsAbortSig P κ Msg recom) eX eY PD K B)))).1
  rw [qDistAdv, hE] at h
  rw [qDistAdv, hE]
  calc _ ≤ _ := h
    _ ≤ _ := by
      rw [add_comm]
      gcongr
      exact fsAborts_nma_lossy_avg_le P recom D₁ ε_ls hls eX eY B

end Hop

end CatCrypt.Quantum.QROM
