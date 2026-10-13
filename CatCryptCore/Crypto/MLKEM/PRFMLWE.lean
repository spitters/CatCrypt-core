/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.PRFKEMChain
public import CatCryptCore.Quantum.QROM.PolyOracle

/-!
# The IND-CPA term of the `PRF_η` chain under quantum module-LWE

The averaged bounds of `PRFKEMChain` and `PRFCoinWeak` contain the IND-CPA
advantage of the adversary `redAdv b₀ A` in the experiment `qIndAuxIdealPr`,
whose key and challenge noise are uniform rows and whose oracle `auxOracleF`
answers the merged oracle of `prfScheme F` and the table `F`. This module bounds
that advantage by module-LWE and extended module-LWE advantages of quantum
distinguishers without oracle access.

Averaged over the tables `G`, `J`, `Hq`, `T`, `F` and the seed `z`, the
acceptance probability of the adversary is a `[0, 1]`-valued function `viewF`
of its classical view. When key generation and encryption at uniform noise rows
sample the key and the ciphertext of a module-LWE K-PKE (`hKey`, `hEnc`), the
IND-CPA advantage is the distance of the expectations of `viewF` in that
scheme, and `cpaExp_absDiff_le` bounds it by four module-LWE distances. Each
distance is the advantage of a reduction that draws polynomial coefficients,
evaluates the six tables from them, and runs the adversary once
(`prOut_avg_eq_of_kWise` through `KWiseInvariant.push`).

The oracle answer on the public-key slice re-encrypts under the row of `F` at
the coin of the `G`-value, so it reads `|Nc|` points of `F`; the table `F` is
replaced by a polynomial of degree `< prfDeg q k Nc = 2 q' |Nc|`,
`q' = flatQ q k q`.

## Main definitions

* `ReadsAtMost r Φ` — every value of `Φ H` is determined by `H` at `r` points
* `redProgK` — the program of `redAdv` with the challenge key as a parameter
* `runF`, `viewF` — one run of an adversary of `PRFAuxHop` against
  `auxOracleF`, and its average over the tables and the seed
* `prfDeg q k Nc` — the independence degree of the polynomial for `F`
* `qRedEncF`, `qRedExtF` — the reductions with self-sampled oracles
* `qMLWEPrfBound` — their four module-LWE advantages at polynomial oracles
* `owTermStd` — `owTerm` with the ideal IND-CPA advantage replaced by the four
  module-LWE advantages

## Main results

* `kWiseInvariant_prOut_readsAtMost` — the acceptance probability of a fixed
  adversary against an oracle reading `r` points per answer is invariant under
  `2 q r`-wise independent tables
* `viewF_redAdv_eq_push` — the average over uniform tables equals the average
  over `k`-wise independent seeded families
* `qIndAuxIdealPr_eq_cpaExp` — the ideal experiment is `cpaExp` of `viewF`
* `absDiff_qIndAuxIdealPr_le_qMLWE` — the ideal IND-CPA advantage of
  `redAdv b₀ A` is at most two module-LWE and two extended module-LWE
  advantages of `qRedEncF` and `qRedExtF`; `MLKEM512QROMPrf` carries it into
  `owTermStd` when key generation is only close to the K-PKE

## The model

The reductions `qRedEncF` and `qRedExtF` hold no table: each draws `auxDeg q k` field elements for each of
`G`, `J`, `Hq`, `T`, `prfDeg q k Nc` for `F`, and evaluates the polynomials at
the points it needs. The hypotheses `hKey` and `hEnc` state that the row
assemblies `kg ∘ eK` and `enc` at uniform rows have the distributions of the
key and the ciphertext of `mapCiphertext (toScheme P) f g`.

## References

* [Zhandry — Secure Identity-Based Encryption in the Quantum Random Oracle
  Model, CRYPTO 2012], Theorem 6.1
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal NNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.QROM
open CatCrypt.Crypto.PKE.Games (Scheme)
open CatCrypt.Crypto.MLKEM.PRFOracle (avg avg_prod avg_le_one prfRow)
open CatCrypt.Crypto.MLKEM.PRFAuxHop (prfScheme auxOracleF auxRd auxOracleF_local QIndAuxPrfAdv
  qIndAuxIdealPr auxView AuxSide)
open CatCrypt.Crypto.MLKEM.PRFKEMChain (redProg redAdv avg_equiv owTerm prfHop
  qINDCCAAdvantageF)
open CatCrypt.Quantum.QROM.PRFChain (chainBound)

noncomputable section

namespace CatCrypt.Crypto.MLKEM.PRFMLWE

/-! ## Oracles whose answers read several points -/

section Reads

variable {α β γ δ : Type}

/-- Every value of `Φ H` is determined by `H` at `r` points at most. -/
def ReadsAtMost (r : ℕ) (Φ : (α → β) → γ → δ) : Prop :=
  ∀ y, ∃ S : Finset α, S.card ≤ r ∧ ∀ H H' : α → β, (∀ x ∈ S, H x = H' x) → Φ H y = Φ H' y

theorem dependsOnAtMost_comp_readsAtMost {k r : ℕ} {F : (γ → δ) → ℂ}
    (hF : DependsOnAtMost k F) {Φ : (α → β) → γ → δ} (hΦ : ReadsAtMost r Φ) :
    DependsOnAtMost (k * r) (fun H => F (Φ H)) := by
  classical
  choose T hT hTΦ using hΦ
  obtain ⟨ι, _, S, g, hg, hF⟩ := hF
  refine ⟨ι, inferInstance, fun i => (S i).biUnion T, fun i H => g i (Φ H),
    fun i => ⟨?_, ?_⟩, fun H => hF (Φ H)⟩
  · exact (Finset.card_biUnion_le_card_mul _ _ r fun y _ => hT y).trans
      (Nat.mul_le_mul_right r (hg i).1)
  · intro H H' hH
    exact (hg i).2 _ _ fun y hy => hTΦ y H H' fun x hx => hH x (Finset.mem_biUnion.mpr ⟨y, hy, hx⟩)

theorem entriesDependOnAtMost_comp_readsAtMost {d k r : ℕ}
    {M : (γ → δ) → Matrix (Fin d) (Fin d) ℂ} (hM : EntriesDependOnAtMost k M)
    {Φ : (α → β) → γ → δ} (hΦ : ReadsAtMost r Φ) :
    EntriesDependOnAtMost (k * r) (fun H => M (Φ H)) :=
  fun i j => dependsOnAtMost_comp_readsAtMost (hM i j) hΦ

/-- A chain with `q` calls to an oracle whose entries read `r` points has entries
reading `q r` points. -/
theorem chainOp_entries_dependsOn_of_reads {d r : ℕ} (O : (α → β) → Matrix (Fin d) (Fin d) ℂ)
    (hO : EntriesDependOnAtMost r O) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      EntriesDependOnAtMost (q * r) (fun H => chainOp (O H) q U)
  | 0, U => EntriesDependOnAtMost.const _ (U 0 : Matrix (Fin d) (Fin d) ℂ)
  | q + 1, U =>
    ((chainOp_entries_dependsOn_of_reads O hO q (Fin.tail U)).mul hO le_rfl).mul
      (EntriesDependOnAtMost.const 0 (U 0 : Matrix (Fin d) (Fin d) ℂ))
      (le_of_eq (by ring))

/-- The merged oracle `mergeOracle (O H) F` reads one point of `H` when `O` does. -/
theorem readsOne_mergeOracle {m m' n : ℕ} (O : (α → β) → Fin m → Fin n) (hO : ReadsOne O)
    (F : Fin m' → Fin n) : ReadsOne fun H => mergeOracle (O H) F := by
  intro y
  induction y using Fin.addCases with
  | left x =>
    obtain ⟨S, hS, h⟩ := hO x
    exact ⟨S, hS, fun H H' hH => by simp only [mergeOracle_castAdd]; exact h H H' hH⟩
  | right x => exact ⟨∅, by simp, fun _ _ _ => by simp only [mergeOracle_natAdd]⟩

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {m n w j : ℕ} [NeZero n]

/-- The acceptance probability of a `j`-query adversary against an oracle each
of whose values reads `r` points of the table is invariant under every
`K`-wise independent weight, for `K ≥ 2 j r`. -/
theorem kWiseInvariant_prOut_readsAtMost [Nonempty β] (A : QAdv m n w j)
    (O : (α → β) → Fin m → Fin n) {r : ℕ} (hO : ReadsAtMost r O) {K : ℕ}
    (hK : 2 * (j * r) ≤ K) : KWiseInvariant K (fun H => prOut A (O H)) := by
  have hOr : EntriesDependOnAtMost (1 * r)
      (fun H => (oracleU m n w (O H) : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ)) :=
    entriesDependOnAtMost_comp_readsAtMost (oracleU_entries_dependsOn m n w) hO
  rw [one_mul] at hOr
  have hX : EntriesDependOnAtMost (j * r) (fun H => A.final * runOp A (O H)) :=
    (EntriesDependOnAtMost.const 0 A.final).mul
      (chainOp_entries_dependsOn_of_reads _ hOr j A.U) (by omega)
  have hC : DependsOnAtMost (2 * (j * r)) (fun H => prOutC A (O H)) :=
    ((hX.mul (EntriesDependOnAtMost.const 0 A.init.val) (r := j * r) (by omega)).mul
      hX.conjTranspose (by omega)).trace
  have e : (fun H => prOut A (O H)) = fun H => ENNReal.ofReal (prOutC A (O H)).re :=
    funext fun H => prOut_eq_ofReal_re _ _
  rw [e]
  exact (KWiseInvariant.of_dependsOn hC fun H => prOutC_re_nonneg _ _).mono hK

end Reads

/-! ## The oracle `auxOracleF` table by table -/

section OracleReads

variable {Sd Nc PK SK M C KS K Hash Z Φ : Type} {m₁ m₂ m₃ n : ℕ} [Fintype Φ] [Nonempty Φ]
  [Fintype Sd] [Nonempty Sd] [DecidableEq Z] [DecidableEq Hash]
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → PK × SK) (enc : PK → M → (Nc → Fin n) → C)
  (dec : SK → C → Option M) (eK : (Nc → Fin n) → KS)
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × Sd) ≃ Fin n)

theorem readsOne_auxOracleF_G (F : Fin m₃ → Fin n) (pk : PK) (Hq : C → K) (J : Fin m₂ → Fin n)
    (T : C → Fin n) (z : Z) :
    ReadsOne fun G => auxOracleF eD kg enc dec eK hpk eG eJ eKR F pk Hq G J T z :=
  readsOne_mergeOracle _
    (readsOne_auxOracle_G (prfScheme eD kg enc dec eK id F) hpk eG eJ eKR pk Hq J T z) F

theorem readsOne_auxOracleF_J (F : Fin m₃ → Fin n) (pk : PK) (Hq : C → K) (G : Fin m₁ → Fin n)
    (T : C → Fin n) (z : Z) :
    ReadsOne fun J => auxOracleF eD kg enc dec eK hpk eG eJ eKR F pk Hq G J T z :=
  readsOne_mergeOracle _
    (readsOne_auxOracle_J (prfScheme eD kg enc dec eK id F) hpk eG eJ eKR pk Hq G T z) F

theorem readsOne_auxOracleF_T (F : Fin m₃ → Fin n) (pk : PK) (Hq : C → K) (G : Fin m₁ → Fin n)
    (J : Fin m₂ → Fin n) (z : Z) :
    ReadsOne fun T => auxOracleF eD kg enc dec eK hpk eG eJ eKR F pk Hq G J T z :=
  readsOne_mergeOracle _
    (readsOne_auxOracle_T (prfScheme eD kg enc dec eK id F) hpk eG eJ eKR pk Hq G J z) F

theorem readsOne_auxOracleF_Hq (F : Fin m₃ → Fin n) (pk : PK) (G : Fin m₁ → Fin n)
    (J : Fin m₂ → Fin n) (T : C → Fin n) (z : Z) :
    ReadsOne fun Hq => auxOracleF eD kg enc dec eK hpk eG eJ eKR F pk Hq G J T z :=
  readsOne_mergeOracle _
    (readsOne_auxOracle_Hq (prfScheme eD kg enc dec eK id F) hpk eG eJ eKR pk G J T z) F

/-- Every answer of `auxOracleF` reads at most one row of `F`: `|Nc|` points. -/
theorem readsAtMost_auxOracleF_F [Fintype Nc] (pk : PK) (Hq : C → K) (G : Fin m₁ → Fin n)
    (J : Fin m₂ → Fin n) (T : C → Fin n) (z : Z) :
    ReadsAtMost (Fintype.card Nc)
      fun F => auxOracleF eD kg enc dec eK hpk eG eJ eKR F pk Hq G J T z := by
  classical
  intro t
  refine ⟨(auxRd eD hpk eG eKR pk G t).elim ∅ fun s => Finset.univ.image fun N => eD (s, N),
    ?_, fun F F' h => auxOracleF_local eD kg enc dec eK hpk eG eJ eKR pk Hq G J T z F F' t
      fun s hs => ?_⟩
  · cases auxRd eD hpk eG eKR pk G t with
    | none => simp
    | some s => exact Finset.card_image_le.trans (by simp)
  · rw [hs] at h
    funext N
    exact h _ (by simp)

end OracleReads

/-! ## The program of `redAdv` reads few points of `Hq` -/

section ProgReads

open CatCrypt.Quantum.QROM.PRFAdvEmbed (padQ pullS)

variable {m₁ m₂ m₃ n w q k c a : ℕ} {PK C K M Hash : Type} [DecidableEq M] [Nonempty M] [Nonempty K]
  [DecidableEq C] (eG : (M × Hash) ≃ Fin m₁) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero c] [NeZero (m₁ + m₂)]

/-- The program of `redAdv` with the challenge key `h` given as a parameter and
the decapsulation answers read from `Hq`. -/
def redProgK (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (pk : PK) (cst : C) (h : K)
    (Hq : C → K) (x : M × M × (K × Fin (flatQ q k q))) :
    QAdv ((m₁ + m₂) + m₃) n (ancW c k (2 * w)) (flatQ q k q) :=
  padQ (flatQ q k q) x.2.2.2.isLt.le
    (queryPrefix (toQAdv (A.run pk cst h) (decapsHq eC eKa Hq cst))
      (pullS 0 (msgSet (m₂ := m₂) eG x.2.1)) x.2.2.2)

theorem redProg_eq_redProgK (b₀ : Bool) (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (pk : PK)
    (cst : C) (Hq : C → K) (x : M × M × (K × Fin (flatQ q k q))) :
    redProg eG eC eKa b₀ A pk cst Hq x =
      redProgK eG eC eKa A pk cst (if b₀ then Hq cst else x.2.2.1) Hq x := rfl

/-- Every unitary of `redProgK` reads at most `k` points of `Hq`. -/
theorem redProgK_U_dependsOn (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (pk : PK) (cst : C)
    (h : K) (x : M × M × (K × Fin (flatQ q k q))) (i : Fin (flatQ q k q + 1)) :
    EntriesDependOnAtMost k (fun Hq => ((redProgK eG eC eKa A pk cst h Hq x).U i :
      Matrix (Fin (((m₁ + m₂) + m₃) * n * ancW c k (2 * w)))
        (Fin (((m₁ + m₂) + m₃) * n * ancW c k (2 * w))) ℂ)) := by
  by_cases hi : (i : ℕ) ≤ x.2.2.2
  · simp only [redProgK, padQ, dif_pos hi, queryPrefix, toQAdv]
    exact (flatten_family_dependsOn (fun Hq => decapsHq eC eKa Hq cst)
      (readsOne_decapsHq eC eKa cst) k (fun _ => (A.run pk cst h).toMRH)
      (A.run pk cst h).rounds 0 (fun _ => rfl) (fun _ => EntriesDependOnAtMost.const 0 _)
      (fun _ _ => EntriesDependOnAtMost.const 0 _) _).mono (by omega)
  · simp only [redProgK, padQ, dif_neg hi]
    exact EntriesDependOnAtMost.const k _

theorem redProgK_init (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (pk : PK) (cst : C)
    (h : K) (Hq Hq' : C → K) (x : M × M × (K × Fin (flatQ q k q))) :
    (redProgK eG eC eKa A pk cst h Hq x).init = (redProgK eG eC eKa A pk cst h Hq' x).init :=
  flatten_init_eq _ _ k _ _ rfl

end ProgReads

/-! ## One run against `auxOracleF`, table by table -/

/-- The independence degree of the polynomial that replaces `F`: twice the
number `flatQ q k q` of queries times the `|Nc|` points of `F` one answer
reads. -/
def prfDeg (q k : ℕ) (Nc : Type) [Fintype Nc] : ℕ := 2 * (flatQ q k q * Fintype.card Nc)

section Run

variable {Sd Nc PK SK M C KS K Hash Z Φ ι : Type} {m₁ m₂ m₃ n W Q : ℕ} [Fintype Φ] [Nonempty Φ]
  [Fintype Sd] [Nonempty Sd] [DecidableEq Z] [DecidableEq Hash] [NeZero n]
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → PK × SK) (enc : PK → M → (Nc → Fin n) → C)
  (dec : SK → C → Option M) (eK : (Nc → Fin n) → KS)
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × Sd) ≃ Fin n)

/-- The probability that `B` with coins `i` outputs `1` on the public key `pk`
and the challenge ciphertext `cst`, against `auxOracleF` at the tables `Hq`, `G`,
`J`, `T`, the seed `z` and the table `F`. -/
def runF (B : QIndAuxPrfAdv ι m₁ m₂ m₃ n W Q PK C K M) (pk : PK) (cst : C) (i : ι)
    (Hq : C → K) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n) (T : C → Fin n) (z : Z)
    (F : Fin m₃ → Fin n) : ℝ≥0∞ :=
  prOut (B.prog pk cst Hq i) (auxOracleF eD kg enc dec eK hpk eG eJ eKR F pk Hq G J T z)

variable [Fintype Z] [Fintype C] [DecidableEq C] [Fintype K]

/-- The acceptance probability of `B` with coins `i` at the public key `pk` and
the challenge ciphertext `cst`, averaged over the seed and the tables `G`, `J`,
`Hq`, `T`, `F`. -/
def viewF (B : QIndAuxPrfAdv ι m₁ m₂ m₃ n W Q PK C K M) (pk : PK) (i : ι) (cst : C) : ℝ≥0∞ :=
  avg fun z : Z => avg fun G : Fin m₁ → Fin n => avg fun J : Fin m₂ → Fin n =>
    avg fun Hq : C → K => avg fun T : C → Fin n => avg fun F : Fin m₃ → Fin n =>
      runF eD kg enc dec eK hpk eG eJ eKR B pk cst i Hq G J T z F

/-- `viewF` is at most `1`. -/
theorem viewF_le_one [Nonempty Z] [Nonempty K] (B : QIndAuxPrfAdv ι m₁ m₂ m₃ n W Q PK C K M)
    (pk : PK) (i : ι) (cst : C) :
    viewF eD kg enc dec eK hpk eG eJ eKR B pk i cst ≤ 1 :=
  avg_le_one fun _ => avg_le_one fun _ => avg_le_one fun _ => avg_le_one fun _ =>
    avg_le_one fun _ => avg_le_one fun _ => prTrue_Q_le_one _ _

variable [Fintype ι] [Fintype Nc] [DecidableEq Nc]

/-- The ideal experiment is the average over the public coins and the key noise
row, the adversary coins and the challenge noise row of `viewF` at the public
key and the challenge ciphertext. -/
theorem qIndAuxIdealPr_eq_avg (B : QIndAuxPrfAdv ι m₁ m₂ m₃ n W Q PK C K M) (b : Bool) :
    qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR B b =
      avg fun p : Φ × (Nc → Fin n) => avg fun i : ι => avg fun ρ : Nc → Fin n =>
        viewF eD kg enc dec eK hpk eG eJ eKR B (kg p.1 (eK p.2)).1 i
          (enc (kg p.1 (eK p.2)).1 (B.msg (kg p.1 (eK p.2)).1 i b) ρ) := by
  have hL : qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR B b =
      avg fun s : AuxSide Φ ι Z C K m₁ m₂ n × ((Nc → Fin n) × (Nc → Fin n) × (Fin m₃ → Fin n)) =>
        runF eD kg enc dec eK hpk eG eJ eKR B (auxView kg enc eK B b s.1 s.2.1 s.2.2.1).1
          (auxView kg enc eK B b s.1 s.2.1 s.2.2.1).2 s.1.2.1 s.1.2.2.2.2.2.1 s.1.2.2.2.1
          s.1.2.2.2.2.1 s.1.2.2.2.2.2.2 s.1.2.2.1 s.2.2.2 := by
    unfold qIndAuxIdealPr
    symm
    rw [avg_prod]
    rfl
  have hR : (avg fun p : Φ × (Nc → Fin n) => avg fun i : ι => avg fun ρ : Nc → Fin n =>
        viewF eD kg enc dec eK hpk eG eJ eKR B (kg p.1 (eK p.2)).1 i
          (enc (kg p.1 (eK p.2)).1 (B.msg (kg p.1 (eK p.2)).1 i b) ρ)) =
      avg fun t : (Φ × (Nc → Fin n)) × ι × (Nc → Fin n) × Z × (Fin m₁ → Fin n) ×
          (Fin m₂ → Fin n) × (C → K) × (C → Fin n) × (Fin m₃ → Fin n) =>
        runF eD kg enc dec eK hpk eG eJ eKR B (kg t.1.1 (eK t.1.2)).1
          (enc (kg t.1.1 (eK t.1.2)).1 (B.msg (kg t.1.1 (eK t.1.2)).1 t.2.1 b) t.2.2.1) t.2.1
          t.2.2.2.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.2.1 t.2.2.2.1
          t.2.2.2.2.2.2.2.2 := by
    simp only [avg_prod, viewF]
  let e : ((Φ × (Nc → Fin n)) × ι × (Nc → Fin n) × Z × (Fin m₁ → Fin n) ×
          (Fin m₂ → Fin n) × (C → K) × (C → Fin n) × (Fin m₃ → Fin n)) ≃
      AuxSide Φ ι Z C K m₁ m₂ n × ((Nc → Fin n) × (Nc → Fin n) × (Fin m₃ → Fin n)) :=
    { toFun := fun t => ((t.1.1, t.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
          t.2.2.2.2.2.2.2.1), (t.1.2, t.2.2.1, t.2.2.2.2.2.2.2.2))
      invFun := fun s => ((s.1.1, s.2.1), s.1.2.1, s.2.2.1, s.1.2.2.1, s.1.2.2.2.1,
          s.1.2.2.2.2.1, s.1.2.2.2.2.2.1, s.1.2.2.2.2.2.2, s.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hL, hR, ← avg_equiv e]
  rfl

/-- **The ideal experiment is an IND-CPA expectation of `viewF`.** When the key
noise row at uniform public coins gives the public key of `S` (`hKey`) and the
encryption at a uniform noise row gives the ciphertext of `S` (`hEnc`), the
ideal experiment is `cpaExp S` of the function `viewF` of the view. -/
theorem qIndAuxIdealPr_eq_cpaExp {SK' R : Type} [Fintype PK] [Fintype SK'] [Fintype R]
    (S : Scheme PK SK' M C R)
    (hKey : ∀ g : PK → ℝ≥0∞, (avg fun p : Φ × (Nc → Fin n) => g (kg p.1 (eK p.2)).1) =
      ∑ ks : PK × SK', S.keygen ks * g ks.1)
    (hEnc : ∀ (pk : PK) (m : M) (g : C → ℝ≥0∞),
      (avg fun ρ : Nc → Fin n => g (enc pk m ρ)) = avg fun r : R => g (S.enc pk m r))
    (B : QIndAuxPrfAdv ι m₁ m₂ m₃ n W Q PK C K M) (b : Bool) :
    qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR B b =
      cpaExp S B.msgs (viewF eD kg enc dec eK hpk eG eJ eKR B) b := by
  rw [qIndAuxIdealPr_eq_avg]
  have h1 : ∀ (pk : PK) (i : ι),
      (avg fun ρ : Nc → Fin n =>
        viewF eD kg enc dec eK hpk eG eJ eKR B pk i (enc pk (B.msg pk i b) ρ)) =
      avg fun r : R => viewF eD kg enc dec eK hpk eG eJ eKR B pk i (S.enc pk (B.msg pk i b) r) :=
    fun pk i => hEnc pk _ (fun cst => viewF eD kg enc dec eK hpk eG eJ eKR B pk i cst)
  simp only [h1]
  exact hKey fun pk => avg fun i : ι => avg fun r : R =>
    viewF eD kg enc dec eK hpk eG eJ eKR B pk i (S.enc pk (B.msg pk i b) r)

end Run

section Inv

variable {Sd Nc PK SK M C KS K Hash Z Φ : Type} {m₁ m₂ m₃ n w q k c a : ℕ} [Fintype Φ]
  [Nonempty Φ] [Fintype Sd] [Nonempty Sd] [DecidableEq Z] [DecidableEq Hash] [NeZero n]
  [Fintype C] [DecidableEq C] [Fintype K] [DecidableEq K] [Nonempty K] [DecidableEq M]
  [Nonempty M] [NeZero c] [NeZero (m₁ + m₂)]
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → PK × SK) (enc : PK → M → (Nc → Fin n) → C)
  (dec : SK → C → Option M) (eK : (Nc → Fin n) → KS)
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × Sd) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  (b₀ : Bool) (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (pk : PK) (cst : C)
  (x : M × M × (K × Fin (flatQ q k q)))

omit [Fintype C] [Fintype K] [DecidableEq K] in
theorem kWiseInvariant_runF_G (Hq : C → K) (J : Fin m₂ → Fin n) (T : C → Fin n) (z : Z)
    (F : Fin m₃ → Fin n) : KWiseInvariant (auxDeg q k) fun G =>
      runF eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A) pk cst x Hq G J T z F :=
  kWiseInvariant_prOut_family (fun _ => redProg eG eC eKa b₀ A pk cst Hq x)
    (fun G => auxOracleF eD kg enc dec eK hpk eG eJ eKR F pk Hq G J T z)
    (readsOne_auxOracleF_G eD kg enc dec eK hpk eG eJ eKR F pk Hq J T z) 0
    (fun _ => EntriesDependOnAtMost.const 0 _) _ _ (fun _ => rfl) (fun _ => rfl)
    ((Nat.le_add_left _ 1).trans (le_auxDeg le_rfl (Nat.zero_le k)))

omit [Fintype C] [Fintype K] [DecidableEq K] in
theorem kWiseInvariant_runF_J (Hq : C → K) (G : Fin m₁ → Fin n) (T : C → Fin n) (z : Z)
    (F : Fin m₃ → Fin n) : KWiseInvariant (auxDeg q k) fun J =>
      runF eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A) pk cst x Hq G J T z F :=
  kWiseInvariant_prOut_family (fun _ => redProg eG eC eKa b₀ A pk cst Hq x)
    (fun J => auxOracleF eD kg enc dec eK hpk eG eJ eKR F pk Hq G J T z)
    (readsOne_auxOracleF_J eD kg enc dec eK hpk eG eJ eKR F pk Hq G T z) 0
    (fun _ => EntriesDependOnAtMost.const 0 _) _ _ (fun _ => rfl) (fun _ => rfl)
    ((Nat.le_add_left _ 1).trans (le_auxDeg le_rfl (Nat.zero_le k)))

omit [Fintype K] [DecidableEq K] in
theorem kWiseInvariant_runF_T (Hq : C → K) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n) (z : Z)
    (F : Fin m₃ → Fin n) : KWiseInvariant (auxDeg q k) fun T =>
      runF eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A) pk cst x Hq G J T z F :=
  kWiseInvariant_prOut_family (fun _ => redProg eG eC eKa b₀ A pk cst Hq x)
    (fun T => auxOracleF eD kg enc dec eK hpk eG eJ eKR F pk Hq G J T z)
    (readsOne_auxOracleF_T eD kg enc dec eK hpk eG eJ eKR F pk Hq G J z) 0
    (fun _ => EntriesDependOnAtMost.const 0 _) _ _ (fun _ => rfl) (fun _ => rfl)
    ((Nat.le_add_left _ 1).trans (le_auxDeg le_rfl (Nat.zero_le k)))

omit [Fintype C] [Fintype K] [DecidableEq K] in
theorem kWiseInvariant_runF_F [Fintype Nc] (Hq : C → K) (G : Fin m₁ → Fin n)
    (J : Fin m₂ → Fin n) (T : C → Fin n) (z : Z) : KWiseInvariant (prfDeg q k Nc) fun F =>
      runF eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A) pk cst x Hq G J T z F :=
  kWiseInvariant_prOut_readsAtMost (redProg eG eC eKa b₀ A pk cst Hq x)
    (fun F => auxOracleF eD kg enc dec eK hpk eG eJ eKR F pk Hq G J T z)
    (readsAtMost_auxOracleF_F eD kg enc dec eK hpk eG eJ eKR pk Hq G J T z) le_rfl

theorem kWiseInvariant_runF_Hq (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n) (T : C → Fin n)
    (z : Z) (F : Fin m₃ → Fin n) : KWiseInvariant (auxDeg q k) fun Hq =>
      runF eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A) pk cst x Hq G J T z F := by
  set κ : (C → K) → K := fun Hq => if b₀ then Hq cst else x.2.2.1 with hκ
  have e : (fun Hq =>
      runF eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A) pk cst x Hq G J T z F) =
      fun Hq => ∑ h : K, ENNReal.ofReal (((if κ Hq = h then (1 : ℂ) else 0) *
        prOutC (redProgK eG eC eKa A pk cst h Hq x)
          (auxOracleF eD kg enc dec eK hpk eG eJ eKR F pk Hq G J T z))).re := by
    funext Hq
    rw [Finset.sum_eq_single (κ Hq)]
    · rw [if_pos rfl, one_mul, ← prOut_eq_ofReal_re]
      rfl
    · intro h _ hh
      rw [if_neg (Ne.symm hh), zero_mul, Complex.zero_re, ENNReal.ofReal_zero]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  rw [e]
  refine KWiseInvariant.sum Finset.univ _ fun h _ => ?_
  have hind : DependsOnAtMost 1 (fun Hq : C → K => if κ Hq = h then (1 : ℂ) else 0) :=
    DependsOnAtMost.of_localOn (S := {cst}) (by simp) fun H H' hH => by
      simp only [hκ, hH cst (Finset.mem_singleton_self cst)]
  have hrun := prOutC_family_dependsOn (fun Hq => redProgK eG eC eKa A pk cst h Hq x)
    (fun Hq => auxOracleF eD kg enc dec eK hpk eG eJ eKR F pk Hq G J T z)
    (readsOne_auxOracleF_Hq eD kg enc dec eK hpk eG eJ eKR F pk G J T z) k
    (redProgK_U_dependsOn eG eC eKa A pk cst h x)
    (redProgK eG eC eKa A pk cst h (fun _ => h) x).init.val _
    (fun Hq => congrArg (fun D => D.val) (redProgK_init eG eC eKa A pk cst h _ _ x))
    (fun _ => rfl)
  refine (KWiseInvariant.of_dependsOn (hind.mul hrun le_rfl) fun Hq => ?_).mono
    (le_auxDeg le_rfl le_rfl)
  split_ifs
  · rw [one_mul]; exact prOutC_re_nonneg _ _
  · simp

variable [Fintype Z] [Fintype Nc]
  {ΩG ΩJ ΩH ΩT ΩF : Type} [Fintype ΩG] [Nonempty ΩG] [Fintype ΩJ] [Nonempty ΩJ]
  [Fintype ΩH] [Nonempty ΩH] [Fintype ΩT] [Nonempty ΩT] [Fintype ΩF] [Nonempty ΩF]
  (ΦG : ΩG → Fin m₁ → Fin n) (ΦJ : ΩJ → Fin m₂ → Fin n) (ΦH : ΩH → C → K)
  (ΦT : ΩT → C → Fin n) (ΦF : ΩF → Fin m₃ → Fin n)

/-- The average of one run of `redAdv b₀ A` over the uniform tables equals its
average over seeded families, `auxDeg q k`-wise independent for `G`, `J`, `Hq`,
`T` and `prfDeg q k Nc`-wise independent for `F`. -/
theorem viewF_redAdv_eq_push (hG : KWiseIndep (auxDeg q k) (pushWeight ΦG))
    (hJ : KWiseIndep (auxDeg q k) (pushWeight ΦJ)) (hH : KWiseIndep (auxDeg q k) (pushWeight ΦH))
    (hT : KWiseIndep (auxDeg q k) (pushWeight ΦT))
    (hF : KWiseIndep (prfDeg q k Nc) (pushWeight ΦF)) :
    viewF eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A) pk x cst =
      avg fun z : Z => avg fun ωG => avg fun ωJ => avg fun ωH => avg fun ωT => avg fun ωF =>
        runF eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A) pk cst x (ΦH ωH) (ΦG ωG)
          (ΦJ ωJ) (ΦT ωT) z (ΦF ωF) := by
  unfold viewF avg
  refine Finset.sum_congr rfl fun z _ => congrArg _ ?_
  refine (KWiseInvariant.push ?_ ΦG hG).symm.trans ?_
  · exact KWiseInvariant.avg _ fun J => KWiseInvariant.avg _ fun Hq => KWiseInvariant.avg _
      fun T => KWiseInvariant.avg _ fun F =>
        kWiseInvariant_runF_G eD kg enc dec eK hpk eG eJ eKR eC eKa b₀ A pk cst x Hq J T z F
  refine Finset.sum_congr rfl fun ωG _ => congrArg _ ?_
  refine (KWiseInvariant.push ?_ ΦJ hJ).symm.trans ?_
  · exact KWiseInvariant.avg _ fun Hq => KWiseInvariant.avg _ fun T => KWiseInvariant.avg _
      fun F => kWiseInvariant_runF_J eD kg enc dec eK hpk eG eJ eKR eC eKa b₀ A pk cst x Hq
        (ΦG ωG) T z F
  refine Finset.sum_congr rfl fun ωJ _ => congrArg _ ?_
  refine (KWiseInvariant.push ?_ ΦH hH).symm.trans ?_
  · exact KWiseInvariant.avg _ fun T => KWiseInvariant.avg _ fun F =>
      kWiseInvariant_runF_Hq eD kg enc dec eK hpk eG eJ eKR eC eKa b₀ A pk cst x (ΦG ωG)
        (ΦJ ωJ) T z F
  refine Finset.sum_congr rfl fun ωH _ => congrArg _ ?_
  refine (KWiseInvariant.push ?_ ΦT hT).symm.trans ?_
  · exact KWiseInvariant.avg _ fun F =>
      kWiseInvariant_runF_T eD kg enc dec eK hpk eG eJ eKR eC eKa b₀ A pk cst x (ΦH ωH)
        (ΦG ωG) (ΦJ ωJ) z F
  refine Finset.sum_congr rfl fun ωT _ => congrArg _ ?_
  exact (KWiseInvariant.push
    (kWiseInvariant_runF_F eD kg enc dec eK hpk eG eJ eKR eC eKa b₀ A pk cst x (ΦH ωH)
      (ΦG ωG) (ΦJ ωJ) (ΦT ωT) z) ΦF hF).symm

end Inv

/-! ## The reductions with self-sampled oracles -/

section Red

open CatCrypt.Crypto.MLKEM.CompressedPKE (mapCiphertext)

variable {Sd Nc SK C KS K Hash Z Φ ι : Type} {m₁ m₂ m₃ n W Q : ℕ} [Fintype Φ] [Nonempty Φ]
  [Fintype Sd] [Nonempty Sd] [DecidableEq Z] [DecidableEq Hash] [NeZero n]
  (P : MLWE_PKE_Scheme.Params) (f : MLWE_PKE_Basic.CT P.toBasic → C)
  (g : C → MLWE_PKE_Basic.CT P.toBasic)
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → MLWE_PKE_Basic.PK P.toBasic × SK)
  (enc : MLWE_PKE_Basic.PK P.toBasic → P.PT → (Nc → Fin n) → C)
  (dec : SK → C → Option P.PT) (eK : (Nc → Fin n) → KS)
  (hpk : MLWE_PKE_Basic.PK P.toBasic → Hash) (eG : (P.PT × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × Sd) ≃ Fin n)
  {ΩG ΩJ ΩH ΩT ΩF : Type}
  (ΦG : ΩG → Fin m₁ → Fin n) (ΦJ : ΩJ → Fin m₂ → Fin n) (ΦH : ΩH → C → K)
  (ΦT : ΩT → C → Fin n) (ΦF : ΩF → Fin m₃ → Fin n)
  (B : QIndAuxPrfAdv ι m₁ m₂ m₃ n W Q (MLWE_PKE_Basic.PK P.toBasic) C K P.PT)

/-- The first-hop reduction: on a module-LWE sample `pk = (A, t)` and coins
`(i, r, z, ωG, ωJ, ωH, ωT, ωF)`, it encrypts the message of `B` selected by `b`
under `pk` with coins `r`, forms the tables `ΦG ωG`, `ΦJ ωJ`, `ΦH ωH`, `ΦT ωT`,
`ΦF ωF`, and runs `B` with coins `i`, answering its oracle calls by
`auxOracleF` computed from those tables. -/
def qRedEncF (b : Bool) :
    QStdDist (ι × P.Seed × Z × ΩG × ΩJ × ΩH × ΩT × ΩF) (MLWE_PKE_Basic.PK P.toBasic)
      ((m₁ + m₂) + m₃) n W :=
  fun pk s => absorbOracle
    (B.prog pk ((mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g).enc pk (B.msg pk s.1 b) s.2.1)
      (ΦH s.2.2.2.2.2.1) s.1)
    (auxOracleF eD kg enc dec eK hpk eG eJ eKR (ΦF s.2.2.2.2.2.2.2) pk (ΦH s.2.2.2.2.2.1)
      (ΦG s.2.2.2.1) (ΦJ s.2.2.2.2.1) (ΦT s.2.2.2.2.2.2.1) s.2.2.1)

/-- The second-hop reduction: on an extended sample `(A, t, u, v)` and coins
`(i, z, ωG, ωJ, ωH, ωT, ωF)`, it forms the ciphertext `f (u, v + encode m)` of
the message of `B` selected by `b`, forms the tables, and runs `B` with coins
`i` on the public key `(A, t)` and that ciphertext, answering its oracle calls
by `auxOracleF` computed from the tables. -/
def qRedExtF (b : Bool) :
    QStdDist (ι × Z × ΩG × ΩJ × ΩH × ΩT × ΩF)
      (P.toBasic.Mat × P.toBasic.Vec × P.toBasic.Vec × P.toBasic.R) ((m₁ + m₂) + m₃) n W :=
  fun x s => absorbOracle
    (B.prog (x.1, x.2.1)
      (f (x.2.2.1, P.toBasic.ring_add x.2.2.2 (P.toBasic.m_encode (B.msg (x.1, x.2.1) s.1 b))))
      (ΦH s.2.2.2.2.1) s.1)
    (auxOracleF eD kg enc dec eK hpk eG eJ eKR (ΦF s.2.2.2.2.2.2) (x.1, x.2.1) (ΦH s.2.2.2.2.1)
      (ΦG s.2.2.1) (ΦJ s.2.2.2.1) (ΦT s.2.2.2.2.2.1) s.2.1)

end Red

/-! ## The acceptance probabilities of the reductions -/

section RedAcc

open CatCrypt.Crypto.MLKEM.CompressedPKE (mapCiphertext)

variable {Sd Nc SK C KS K Hash Z Φ : Type} {m₁ m₂ m₃ n w q k c a : ℕ} [Fintype Φ]
  [Nonempty Φ] [Fintype Sd] [Nonempty Sd] [DecidableEq Z] [DecidableEq Hash] [NeZero n]
  [Fintype C] [DecidableEq C] [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Z]
  [Fintype Nc] [NeZero c] [NeZero (m₁ + m₂)]
  (P : MLWE_PKE_Scheme.Params) (f : MLWE_PKE_Basic.CT P.toBasic → C)
  (g : C → MLWE_PKE_Basic.CT P.toBasic)
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → MLWE_PKE_Basic.PK P.toBasic × SK)
  (enc : MLWE_PKE_Basic.PK P.toBasic → P.PT → (Nc → Fin n) → C)
  (dec : SK → C → Option P.PT) (eK : (Nc → Fin n) → KS)
  (hpk : MLWE_PKE_Basic.PK P.toBasic → Hash) (eG : (P.PT × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × Sd) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  {ΩG ΩJ ΩH ΩT ΩF : Type} [Fintype ΩG] [Nonempty ΩG] [Fintype ΩJ] [Nonempty ΩJ]
  [Fintype ΩH] [Nonempty ΩH] [Fintype ΩT] [Nonempty ΩT] [Fintype ΩF] [Nonempty ΩF]
  (ΦG : ΩG → Fin m₁ → Fin n) (ΦJ : ΩJ → Fin m₂ → Fin n) (ΦH : ΩH → C → K)
  (ΦT : ΩT → C → Fin n) (ΦF : ΩF → Fin m₃ → Fin n)
  (hG : KWiseIndep (auxDeg q k) (pushWeight ΦG)) (hJ : KWiseIndep (auxDeg q k) (pushWeight ΦJ))
  (hH : KWiseIndep (auxDeg q k) (pushWeight ΦH)) (hT : KWiseIndep (auxDeg q k) (pushWeight ΦT))
  (hF : KWiseIndep (prfDeg q k Nc) (pushWeight ΦF))
  (b₀ : Bool) (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a (MLWE_PKE_Basic.PK P.toBasic) C K)

include hG hJ hH hT hF in
/-- The acceptance probability of `qRedEncF` at `redAdv b₀ A` is `encExp` of
`viewF`. -/
theorem qStdAcc_qRedEncF (b : Bool) :
    qStdAcc (qRedEncF P f g eD kg enc dec eK hpk eG eJ eKR ΦG ΦJ ΦH ΦT ΦF
        (redAdv eG eC eKa b₀ A) b) =
      encExp (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g) (redAdv eG eC eKa b₀ A).msgs
        (viewF eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A)) b := by
  funext pk
  simp only [qStdAcc, sum_prod_uniform, prOut0, qRedEncF, prOut_absorbOracle, encExp,
    viewF_redAdv_eq_push eD kg enc dec eK hpk eG eJ eKR eC eKa b₀ A _ _ _ ΦG ΦJ ΦH ΦT ΦF
      hG hJ hH hT hF]
  rfl

include hG hJ hH hT hF in
/-- The acceptance probability of `qRedExtF` at `redAdv b₀ A` is `extView` of
`viewF`. -/
theorem qStdAcc_qRedExtF (b : Bool) :
    qStdAcc (qRedExtF P f eD kg enc dec eK hpk eG eJ eKR ΦG ΦJ ΦH ΦT ΦF
        (redAdv eG eC eKa b₀ A) b) =
      extView P.toBasic f (redAdv eG eC eKa b₀ A).msgs
        (viewF eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A)) b := by
  funext x
  simp only [qStdAcc, sum_prod_uniform, prOut0, qRedExtF, prOut_absorbOracle, extView,
    viewF_redAdv_eq_push eD kg enc dec eK hpk eG eJ eKR eC eKa b₀ A _ _ _ ΦG ΦJ ΦH ΦT ΦF
      hG hJ hH hT hF]
  rfl

end RedAcc

/-! ## The ideal IND-CPA advantage under quantum module-LWE -/

section Bound

open CatCrypt.Crypto.MLKEM.CompressedPKE (mapCiphertext)

variable {Sd Nc SK C KS K Hash Z Φ : Type} {m₁ m₂ m₃ n w q k c a : ℕ} [Fintype Φ]
  [Nonempty Φ] [Fintype Sd] [Nonempty Sd] [DecidableEq Z] [DecidableEq Hash]
  [NeZero n] [Fintype C] [DecidableEq C] [Fintype K] [DecidableEq K] [Nonempty K] [Fintype Z]
  [Nonempty Z] [Fintype Nc] [DecidableEq Nc] [NeZero c] [NeZero (m₁ + m₂)] [NeZero (flatQ q k q)]
  (P : MLWE_PKE_Scheme.Params) (f : MLWE_PKE_Basic.CT P.toBasic → C)
  (g : C → MLWE_PKE_Basic.CT P.toBasic)
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → MLWE_PKE_Basic.PK P.toBasic × SK)
  (enc : MLWE_PKE_Basic.PK P.toBasic → P.PT → (Nc → Fin n) → C)
  (dec : SK → C → Option P.PT) (eK : (Nc → Fin n) → KS)
  (hpk : MLWE_PKE_Basic.PK P.toBasic → Hash) (eG : (P.PT × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × Sd) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  (PG : PolyData (Fin m₁) (Fin n)) (PJ : PolyData (Fin m₂) (Fin n)) (PH : PolyData C K)
  (PT : PolyData C (Fin n)) (PF : PolyData (Fin m₃) (Fin n))

/-- The sum of the two module-LWE and two extended module-LWE advantages of the
reductions `qRedEncF` and `qRedExtF` at `redAdv b₀ A`, with the tables drawn as
polynomials from `PG`, `PJ`, `PH`, `PT` of degree `< auxDeg q k` and from `PF`
of degree `< prfDeg q k Nc`. -/
def qMLWEPrfBound (b₀ : Bool)
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a (MLWE_PKE_Basic.PK P.toBasic) C K) : ℝ≥0∞ :=
  qMLWE P.toBasic (qRedEncF P f g eD kg enc dec eK hpk eG eJ eKR (PG.table (auxDeg q k))
      (PJ.table (auxDeg q k)) (PH.table (auxDeg q k)) (PT.table (auxDeg q k))
      (PF.table (prfDeg q k Nc)) (redAdv eG eC eKa b₀ A) true) +
    qMLWEExt P.toBasic (qRedExtF P f eD kg enc dec eK hpk eG eJ eKR (PG.table (auxDeg q k))
      (PJ.table (auxDeg q k)) (PH.table (auxDeg q k)) (PT.table (auxDeg q k))
      (PF.table (prfDeg q k Nc)) (redAdv eG eC eKa b₀ A) true) +
    qMLWEExt P.toBasic (qRedExtF P f eD kg enc dec eK hpk eG eJ eKR (PG.table (auxDeg q k))
      (PJ.table (auxDeg q k)) (PH.table (auxDeg q k)) (PT.table (auxDeg q k))
      (PF.table (prfDeg q k Nc)) (redAdv eG eC eKa b₀ A) false) +
    qMLWE P.toBasic (qRedEncF P f g eD kg enc dec eK hpk eG eJ eKR (PG.table (auxDeg q k))
      (PJ.table (auxDeg q k)) (PH.table (auxDeg q k)) (PT.table (auxDeg q k))
      (PF.table (prfDeg q k Nc)) (redAdv eG eC eKa b₀ A) false)

/-- **The ideal IND-CPA advantage of `redAdv b₀ A` under quantum module-LWE.**
When key generation and encryption at uniform noise rows sample the key and the
ciphertext of `mapCiphertext (toScheme P) f g`, the IND-CPA advantage of
`redAdv b₀ A` in the experiment with uniform noise rows is at most two
module-LWE and two extended module-LWE advantages, without oracle access, of
the reductions `qRedEncF` and `qRedExtF` with polynomial oracles. -/
theorem absDiff_qIndAuxIdealPr_le_qMLWE
    (hKey : ∀ g' : MLWE_PKE_Basic.PK P.toBasic → ℝ≥0∞,
      (avg fun p : Φ × (Nc → Fin n) => g' (kg p.1 (eK p.2)).1) =
        ∑ ks, (mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g).keygen ks * g' ks.1)
    (hEnc : ∀ (pk : MLWE_PKE_Basic.PK P.toBasic) (m : P.PT) (g' : C → ℝ≥0∞),
      (avg fun ρ : Nc → Fin n => g' (enc pk m ρ)) =
        avg fun r : P.Seed => g' ((mapCiphertext (MLWE_PKE_Scheme.toScheme P) f g).enc pk m r))
    (b₀ : Bool) (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a (MLWE_PKE_Basic.PK P.toBasic) C K) :
    absDiff (qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A) true)
        (qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A) false) ≤
      qMLWEPrfBound P f g eD kg enc dec eK hpk eG eJ eKR eC eKa PG PJ PH PT PF b₀ A := by
  rw [qIndAuxIdealPr_eq_cpaExp eD kg enc dec eK hpk eG eJ eKR _ hKey hEnc,
    qIndAuxIdealPr_eq_cpaExp eD kg enc dec eK hpk eG eJ eKR _ hKey hEnc]
  refine (cpaExp_absDiff_le P f g _ _
    (viewF_le_one eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A))).trans_eq ?_
  simp only [qMLWEPrfBound, qMLWE, qMLWEExt,
    qStdAcc_qRedEncF P f g eD kg enc dec eK hpk eG eJ eKR eC eKa _ _ _ _ _ (PG.kWise _)
      (PJ.kWise _) (PH.kWise _) (PT.kWise _) (PF.kWise _),
    qStdAcc_qRedExtF P f eD kg enc dec eK hpk eG eJ eKR eC eKa _ _ _ _ _ (PG.kWise _)
      (PJ.kWise _) (PH.kWise _) (PT.kWise _) (PF.kWise _)]

variable [Fintype SK]

/-- The one-wayness term `owTerm` with the ideal IND-CPA advantage replaced by
`qMLWEPrfBound`: the four module-LWE advantages of the reductions with
polynomial oracles, the message-space term, twice the `PRF_η` hop and the
averaged decryption error. -/
def owTermStd (b₀ : Bool)
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a (MLWE_PKE_Basic.PK P.toBasic) C K) : ℝ≥0∞ :=
  qMLWEPrfBound P f g eD kg enc dec eK hpk eG eJ eKR eC eKa PG PJ PH PT PF b₀ A +
    (Fintype.card P.PT : ℝ≥0∞)⁻¹ + 2 * prfHop Sd q k +
    avg fun F : Fin m₃ → Fin n => corrErr (prfScheme eD kg enc dec eK id F)

end Bound

end CatCrypt.Crypto.MLKEM.PRFMLWE

end

end
