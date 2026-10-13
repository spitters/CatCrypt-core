/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.PRFChain
public import CatCryptCore.Crypto.MLKEM.PRFAuxHop
public import CatCryptCore.Quantum.QROM.PRFAdvEmbed
public import CatCryptCore.Quantum.QROM.NormalFormPrefix

/-!
# The quantum IND-CCA bound for a KEM adversary that queries the noise table

The KEM adversary of this module queries, besides the oracles `G` and `J`, the
table `F` from which the K-PKE reads its noise (`PRF_η` as a random oracle): its
oracle domain is `(m₁ + m₂) + m₃` and its oracle is `mergeOracle (kemOracle i) F`.
For each table `F` the adversary with `F` built in (`PRFAdvEmbed.hardwire`) is a
KEM adversary of the chain of `PRFChain`, with the winning probability of the
adversary against the merged oracle. The one-wayness terms of that chain,
averaged over the table, are IND-CPA probabilities of an adversary `redAdv` in
the experiment `qIndAuxPrfPr` of `PRFAuxHop`; `redAdv` queries `F` through its
oracle and holds no table.

## Main definitions

* `prWinKEMF`, `qINDCCAAdvantageF` — the IND-CCA game of an adversary whose
  oracle also answers the table `F`
* `redProg`, `redAdv` — the IND-CPA adversary on the extended oracle: the
  adversary run up to the stop query of its coins, the query register measured
  against the points of the second message, padded to `flatQ q k q` queries
* `prfHop`, `owTerm` — the `PRF_η` hop distance and the one-wayness term of the
  final bound

## Main results

* `qINDCCAAdvantage_hardwire` — the hard-wired adversary has the advantage of
  the adversary against the merged oracle
* `avg_qINDCCAF_le` — the average over the table of the advantage is at most the
  weight of the tables outside `ChainGood` plus `chainBound` at the averaged
  one-wayness terms
* `qIndcpaAuxRun_hardwire` — one run of the IND-CPA reduction of the chain is
  one run of `redProg` against the merged oracle
* `avg_qIndcpaAuxPr_eq` — averaged over the table, the IND-CPA probability of
  the reduction of the chain is `qIndAuxPrfPr (redAdv b₀ A)`
* `avg_qINDCCAF_le_ideal` — the average advantage is at most the weight of the
  tables outside `ChainGood` plus `chainBound` at `owTerm`: the IND-CPA
  advantages of `redAdv` in the experiment with uniform noise, the message-space
  term, twice the `PRF_η` hop and the averaged decryption error

## The model

The scheme is `prfScheme eD kg enc dec eK id F` of `PRFAuxHop`. The bounds
`avg_qINDCCAF_le` and `avg_qINDCCAF_le_ideal` carry the weight of the tables
outside `ChainGood` as a term.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.QROM
open CatCrypt.Crypto.PKE.Games (Scheme)
open CatCrypt.Quantum.QROM.PRFChain (chainBound chainBound_mono ChainGood avg_qINDCCA_le
  avg_qOwcpaAux_le_of_close)
open CatCrypt.Quantum.QROM.PRFAdvEmbed (hardwire prOutMR_hardwire prOutPrefixMR_hardwire pullS
  padQ prOut_padQ projS_mul_oracleU tagN)
open CatCrypt.Crypto.MLKEM.PRFOracle (avg avg_prod avg_comm)

noncomputable section

namespace CatCrypt.Crypto.MLKEM.PRFKEMChain

/-! ## The game with the table as a third oracle -/

section Game

variable {m₁ m₂ m₃ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Fintype K] [Nonempty K] [Nonempty R]
  [DecidableEq C] (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero n]

/-- The probability that `A` outputs `1` in the IND-CCA game with bit `b`, the
oracle of `A` answering `kemOracle i` on the first summand and the table `F` on
the second. -/
def prWinKEMF (F : Fin m₃ → Fin n) (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (b : Bool) :
    ℝ≥0∞ :=
  ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
    prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i) (kemKey hpk eG eKR i b))
      (mergeOracle (kemOracle i) F) (kemDecaps P hpk eG eJ eKR eC eKa i)

/-- The IND-CCA advantage of `A` with the table `F` as a third oracle. -/
def qINDCCAAdvantageF (F : Fin m₃ → Fin n) (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) :
    ℝ≥0∞ :=
  CatCrypt.Quantum.absDiff (prWinKEMF P hpk eG eJ eKR eC eKa F A true)
    (prWinKEMF P hpk eG eJ eKR eC eKa F A false)

variable [NeZero (m₁ + m₂)] [NeZero c]

omit [Nonempty M] [Nonempty Z] [Nonempty R] in
theorem prWinKEM_hardwire (F : Fin m₃ → Fin n) (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K)
    (b : Bool) :
    prWinKEM P hpk eG eJ eKR eC eKa (hardwire F A) b = prWinKEMF P hpk eG eJ eKR eC eKa F A b := by
  unfold prWinKEM prWinKEMF
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prOutMR_hardwire]

omit [Nonempty M] [Nonempty Z] [Nonempty R] in
/-- The hard-wired adversary has the advantage of `A` against the merged oracle. -/
theorem qINDCCAAdvantage_hardwire (F : Fin m₃ → Fin n)
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) :
    qINDCCAAdvantage P hpk eG eJ eKR eC eKa (hardwire F A) =
      qINDCCAAdvantageF P hpk eG eJ eKR eC eKa F A := by
  rw [qINDCCAAdvantage, qINDCCAAdvantageF, prWinKEM_hardwire, prWinKEM_hardwire]

end Game

/-! ## The chain bound averaged over the table -/

section Family

variable {m₁ m₂ m₃ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Nonempty R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero n] [NeZero c] [NeZero a] [NeZero (m₁ + m₂)] [NeZero (flatQ q k q)]

open scoped Classical in
/-- **The quantum IND-CCA bound for an adversary that queries the table,
averaged over the table.** For a family of schemes `P F` and an adversary `A`
whose oracle answers `F` on its third summand, the average advantage is at most
the weight of the tables at which `ChainGood (P F) Λ ε` fails, plus `chainBound`
at the averages over `F` of the one-wayness probabilities of the reduction of
the chain applied to `hardwire F A`. -/
theorem avg_qINDCCAF_le (P : (Fin m₃ → Fin n) → Scheme PK SK M C R)
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (Λ ε : ℝ≥0∞) :
    (avg fun F => qINDCCAAdvantageF (P F) hpk eG eJ eKR eC eKa F A) ≤
      (avg fun F => if ChainGood hpk eG eKR (P F) Λ ε then 0 else 1) +
        chainBound (flatQ q k q) (flatQ (q + 4) k q) Λ ε (Fintype.card Z : ℝ≥0∞)⁻¹
          (avg fun F => qOwcpaAux (P F) hpk eG eJ eKR eC eKa
            (owRedQuery (nfKEM (hardwire F A)) true))
          (avg fun F => qOwcpaAux (P F) hpk eG eJ eKR eC eKa
            (owRedQuery (nfKEM (hardwire F A)) false)) := by
  simp only [← qINDCCAAdvantage_hardwire]
  exact avg_qINDCCA_le hpk eG eJ eKR eC eKa P (fun F => hardwire F A) Λ ε

end Family

/-! ## The IND-CPA reduction against the merged oracle -/

section Reduction

variable {m₁ m₂ m₃ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [DecidableEq Z] [Fintype K]
  [Nonempty K] [Fintype R] [Fintype C] [DecidableEq C] [DecidableEq Hash]
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero n] [NeZero c] [NeZero a] [NeZero (m₁ + m₂)]

/-- The IND-CPA adversary program on the extended oracle at the coins
`x = (μ₀, μ₁, κ, j)`: the adversary `A` on the public key, the challenge
ciphertext and the key `Hq cst` at `b₀ = true` or `κ` at `b₀ = false`, with
decapsulation answers `decapsHq Hq cst`, cut at query `j`, measuring whether its
query register lies over the points of the message `μ₁`, padded to
`flatQ q k q` queries. -/
def redProg (b₀ : Bool) (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (pk : PK) (cst : C)
    (Hq : C → K) (x : M × M × (K × Fin (flatQ q k q))) :
    QAdv ((m₁ + m₂) + m₃) n (ancW c k (2 * w)) (flatQ q k q) :=
  padQ (flatQ q k q) x.2.2.2.isLt.le
    (queryPrefix (toQAdv (A.run pk cst (if b₀ then Hq cst else x.2.2.1)) (decapsHq eC eKa Hq cst))
      (pullS 0 (msgSet (m₂ := m₂) eG x.2.1)) x.2.2.2)

omit [Fintype PK] [Fintype SK] [Fintype M] [Fintype Z] [Fintype K] [Fintype R] [Fintype C] in
/-- One run of the IND-CPA reduction of the chain, applied to `hardwire F A`, is
one run of `redProg` against the merged oracle. -/
theorem qIndcpaAuxRun_hardwire (P : Scheme PK SK M C R) (F : Fin m₃ → Fin n)
    (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (b₀ : Bool) (pk : PK) (cst : C)
    (Hq : C → K) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n) (T : C → Fin n) (z : Z)
    (x : M × M × (K × Fin (flatQ q k q))) :
    qIndcpaAuxRun P hpk eG eJ eKR eC eKa (indRed eG (owRedQuery (nfKEM (hardwire F A)) b₀))
        pk cst Hq G J T z x =
      prOut (redProg eG eC eKa b₀ A pk cst Hq x)
        (mergeOracle (auxOracle P hpk eG eJ eKR pk Hq G J T z) F) := by
  unfold qIndcpaAuxRun redProg
  rw [prOut_padQ _ _ _ _ (projS_mul_oracleU _ _)]
  change prOut (queryPrefix (toQAdv ((nfKEM (hardwire F A)).run pk cst
      (if b₀ then Hq cst else x.2.2.1)) (decapsHq eC eKa Hq cst)) (msgSet (m₂ := m₂) eG x.2.1)
      x.2.2.2) _ = _
  rw [prOut_queryPrefix_toQAdv, prOut_queryPrefix_toQAdv, prOutPrefixMR_nfKEM,
    prOutPrefixMR_hardwire]

/-- The IND-CPA adversary on the extended oracle: its coins are two messages, a
fake key and a query index; it runs `redProg`. It holds no table: the table `F`
reaches it only through the oracle. -/
def redAdv (b₀ : Bool) (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) :
    PRFAuxHop.QIndAuxPrfAdv (M × M × (K × Fin (flatQ q k q))) m₁ m₂ m₃ n (ancW c k (2 * w))
      (flatQ q k q) PK C K M where
  msgs _ x := (x.1, x.2.1)
  prog pk cst Hq x := redProg eG eC eKa b₀ A pk cst Hq x
  pure pk cst Hq x :=
    flatten_init_pure (decapsHq eC eKa Hq cst) k
      (A.run pk cst (if b₀ then Hq cst else x.2.2.1)).toMRH
      (A.pure pk cst (if b₀ then Hq cst else x.2.2.1))

end Reduction

/-! ## Averages over the table -/

section Avg

variable {α β : Type} [Fintype α] [Fintype β]

/-- An average is invariant under an equivalence of index sets. -/
theorem avg_equiv (e : α ≃ β) (f : β → ℝ≥0∞) : avg (fun x => f (e x)) = avg f := by
  unfold avg
  rw [Fintype.card_congr e]
  exact Equiv.sum_comp e (fun y => (Fintype.card β : ℝ≥0∞)⁻¹ * f y)

/-- The expectation of `h` under the image of the uniform distribution by `g` is
the average of `h ∘ g`. -/
theorem sum_map_uniform [Nonempty α] [DecidableEq β] (g : α → β) (h : β → ℝ≥0∞) :
    ∑ y, (PMF.map g (PMF.uniformOfFintype α)) y * h y = avg fun x => h (g x) := by
  simp only [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply, Finset.sum_mul, avg]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [ite_mul]

/-- The iterated average over the table, the key coins, the adversary coins, the
encryption coin and the side information, in the order of the IND-CPA game
averaged over the table, equals the iterated average in the order of
`qIndAuxPrfPr`. -/
theorem avg_reorder {Tb Φ Sd ι Z G J Hq T : Type} [Fintype Tb] [Fintype Φ] [Fintype Sd]
    [Fintype ι] [Fintype Z] [Fintype G] [Fintype J] [Fintype Hq] [Fintype T]
    (g : Φ → Sd → Sd → ι → Z → G → J → Hq → T → Tb → ℝ≥0∞) :
    (avg fun F : Tb => avg fun p : Φ × Sd => avg fun x : ι => avg fun r : Sd =>
      avg fun z : Z => avg fun Gt : G => avg fun Jt : J => avg fun Ht : Hq => avg fun Tt : T =>
        g p.1 p.2 r x z Gt Jt Ht Tt F) =
      avg fun ω : Φ × ι × Z × G × J × Hq × T => avg fun sr : Sd × Sd => avg fun F : Tb =>
        g ω.1 sr.1 sr.2 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.1 ω.2.2.2.2.2.2 F := by
  have hL : (avg fun F : Tb => avg fun p : Φ × Sd => avg fun x : ι => avg fun r : Sd =>
      avg fun z : Z => avg fun Gt : G => avg fun Jt : J => avg fun Ht : Hq => avg fun Tt : T =>
        g p.1 p.2 r x z Gt Jt Ht Tt F) =
      avg fun t : Tb × (Φ × Sd) × ι × Sd × Z × G × J × Hq × T =>
        g t.2.1.1 t.2.1.2 t.2.2.2.1 t.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1
          t.2.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2.2 t.1 := by
    simp only [avg_prod]
  have hR : (avg fun ω : Φ × ι × Z × G × J × Hq × T => avg fun sr : Sd × Sd => avg fun F : Tb =>
        g ω.1 sr.1 sr.2 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.1 ω.2.2.2.2.2.2 F) =
      avg fun t : (Φ × ι × Z × G × J × Hq × T) × (Sd × Sd) × Tb =>
        g t.1.1 t.2.1.1 t.2.1.2 t.1.2.1 t.1.2.2.1 t.1.2.2.2.1 t.1.2.2.2.2.1 t.1.2.2.2.2.2.1
          t.1.2.2.2.2.2.2 t.2.2 := by
    simp only [avg_prod]
  let e : Tb × (Φ × Sd) × ι × Sd × Z × G × J × Hq × T ≃
      (Φ × ι × Z × G × J × Hq × T) × (Sd × Sd) × Tb :=
    { toFun := fun t => ((t.2.1.1, t.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
        t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2), (t.2.1.2, t.2.2.2.1), t.1)
      invFun := fun t => (t.2.2, (t.1.1, t.2.1.1), t.1.2.1, t.2.1.2, t.1.2.2.1, t.1.2.2.2.1,
        t.1.2.2.2.2.1, t.1.2.2.2.2.2.1, t.1.2.2.2.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hL, hR]
  exact avg_equiv e (fun t : (Φ × ι × Z × G × J × Hq × T) × (Sd × Sd) × Tb =>
    g t.1.1 t.2.1.1 t.2.1.2 t.1.2.1 t.1.2.2.1 t.1.2.2.2.1 t.1.2.2.2.2.1 t.1.2.2.2.2.2.1
      t.1.2.2.2.2.2.2 t.2.2)

end Avg

/-! ## The reduction in the experiment of `PRFAuxHop` -/

section PRF

open PRFAuxHop PRFOracle

variable {Sd Nc PK SK M C KS K Hash Z Φ : Type} {m₁ m₂ m₃ n w q k c a : ℕ}
  [Fintype Φ] [Nonempty Φ] [Fintype Sd] [DecidableEq Sd] [Nonempty Sd] [Fintype Nc]
  [DecidableEq Nc] [Fintype Z] [Nonempty Z] [DecidableEq Z] [Fintype C] [DecidableEq C]
  [Fintype K] [Nonempty K] [DecidableEq Hash] [Fintype PK] [DecidableEq PK] [Fintype SK]
  [DecidableEq SK] [Fintype M] [DecidableEq M] [Nonempty M]
  [NeZero n] [NeZero c] [NeZero a] [NeZero (m₁ + m₂)]
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → PK × SK) (enc : PK → M → (Nc → Fin n) → C)
  (dec : SK → C → Option M) (eK : (Nc → Fin n) → KS)
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × Sd) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

omit [DecidableEq Sd] [Fintype Nc] [DecidableEq Nc] [Nonempty Z] in
/-- **The one-wayness reduction of the chain, averaged over the table, is the
IND-CPA experiment of `PRFAuxHop` with the adversary `redAdv`.** For the scheme
`prfScheme F`, the average over `F` of the probability that the IND-CPA
reduction of the chain, applied to `hardwire F A`, outputs `1` is
`qIndAuxPrfPr (redAdv b₀ A) b`. -/
theorem avg_qIndcpaAuxPr_eq (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (b₀ b : Bool) :
    (avg fun F : Fin m₃ → Fin n =>
      qIndcpaAuxPr (prfScheme eD kg enc dec eK id F) hpk eG eJ eKR eC eKa
        (indRed eG (owRedQuery (nfKEM (hardwire F A)) b₀)) b) =
      qIndAuxPrfPr eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A) b := by
  have hF : ∀ F : Fin m₃ → Fin n,
      qIndcpaAuxPr (prfScheme eD kg enc dec eK id F) hpk eG eJ eKR eC eKa
        (indRed eG (owRedQuery (nfKEM (hardwire F A)) b₀)) b =
      avg fun p : Φ × Sd => avg fun x : M × M × (K × Fin (flatQ q k q)) => avg fun r : Sd =>
        avg fun z : Z => avg fun G : Fin m₁ → Fin n => avg fun J : Fin m₂ → Fin n =>
          avg fun Hq : C → K => avg fun T : C → Fin n =>
            prOut (redProg eG eC eKa b₀ A (kg p.1 (eK (prfRow eD F p.2))).1
                (enc (kg p.1 (eK (prfRow eD F p.2))).1 (if b then x.2.1 else x.1)
                  (prfRow eD F r)) Hq x)
              (auxOracleF eD kg enc dec eK hpk eG eJ eKR F (kg p.1 (eK (prfRow eD F p.2))).1
                Hq G J T z) := by
    intro F
    rw [qIndcpaAuxPr, prfScheme, sum_map_uniform]
    simp only [qIndcpaAuxRun_hardwire]
    rfl
  simp only [hF]
  refine (avg_reorder (fun (φ : Φ) (σ r : Sd) (x : M × M × (K × Fin (flatQ q k q))) (z : Z)
      (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n) (Hq : C → K) (T : C → Fin n)
      (F : Fin m₃ → Fin n) =>
    prOut (redProg eG eC eKa b₀ A (kg φ (eK (prfRow eD F σ))).1
        (enc (kg φ (eK (prfRow eD F σ))).1 (if b then x.2.1 else x.1) (prfRow eD F r)) Hq x)
      (auxOracleF eD kg enc dec eK hpk eG eJ eKR F (kg φ (eK (prfRow eD F σ))).1 Hq G J T z))).trans
    ?_
  simp only [qIndAuxPrfPr, auxView, QIndAuxPrfAdv.msg, redAdv]

/-- The distance of the `PRF_η` hop at `flatQ q k q` queries. -/
def prfHop (Sd : Type) [Fintype Sd] (q k : ℕ) : ℝ≥0∞ :=
  (Fintype.card Sd : ℝ≥0∞)⁻¹ +
    4 * ((flatQ q k q : ℝ≥0∞) * (8 * (flatQ q k q : ℝ≥0∞) * (Fintype.card Sd : ℝ≥0∞)⁻¹)) ^
      (1 / 2 : ℝ)

/-- The one-wayness term at the bit `b₀`: the IND-CPA advantage of `redAdv b₀ A`
in the experiment with uniform noise rows, the message-space term, twice the
`PRF_η` hop and the averaged decryption error. -/
def owTerm (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (b₀ : Bool) : ℝ≥0∞ :=
  CatCrypt.Quantum.absDiff
      (qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A) true)
      (qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR (redAdv eG eC eKa b₀ A) false) +
    (Fintype.card M : ℝ≥0∞)⁻¹ + 2 * prfHop Sd q k +
    avg fun F : Fin m₃ → Fin n => corrErr (prfScheme eD kg enc dec eK id F)

variable [NeZero (flatQ q k q)]

/-- The averaged one-wayness probability of the chain at the bit `b₀` is at most
`owTerm b₀`. -/
theorem avg_qOwcpaAux_le_owTerm (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (b₀ : Bool) :
    (avg fun F : Fin m₃ → Fin n => qOwcpaAux (prfScheme eD kg enc dec eK id F) hpk eG eJ eKR
      eC eKa (owRedQuery (nfKEM (hardwire F A)) b₀)) ≤
      owTerm eD kg enc dec eK hpk eG eJ eKR eC eKa A b₀ := by
  have h1 := absDiff_qIndAuxPrfPr_qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR
    (redAdv eG eC eKa b₀ A) true
  have h0 := absDiff_qIndAuxPrfPr_qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR
    (redAdv eG eC eKa b₀ A) false
  refine avg_qOwcpaAux_le_of_close hpk eG eJ eKR eC eKa (fun F => prfScheme eD kg enc dec eK id F)
    (fun F => owRedQuery (nfKEM (hardwire F A)) b₀) _ _ (prfHop Sd q k) ?_ ?_
  · rw [avg_qIndcpaAuxPr_eq, add_comm]
    exact tsub_le_iff_right.mp ((le_sup_left).trans h1)
  · rw [avg_qIndcpaAuxPr_eq, add_comm]
    exact tsub_le_iff_right.mp ((le_sup_right).trans h0)

open scoped Classical in
/-- **The quantum IND-CCA bound of the FO KEM over the K-PKE whose noise is read
from a random table that the adversary queries.** For every KEM adversary `A`
whose oracle answers the table `F` on its third summand, the IND-CCA advantage
averaged over `F` is at most the weight of the tables outside `ChainGood`, plus
`chainBound` at `owTerm true` and `owTerm false`: the IND-CPA advantages of
`redAdv b₀ A` in the experiment with uniform noise rows, `|M|⁻¹`, twice the
`PRF_η` hop at `flatQ q k q` queries and the averaged decryption error. -/
theorem avg_qINDCCAF_le_ideal (A : KEMQAdv (m₁ + m₂) m₃ n w q k c a PK C K) (Λ ε : ℝ≥0∞) :
    (avg fun F : Fin m₃ → Fin n =>
      qINDCCAAdvantageF (prfScheme eD kg enc dec eK id F) hpk eG eJ eKR eC eKa F A) ≤
      (avg fun F : Fin m₃ → Fin n =>
        if ChainGood hpk eG eKR (prfScheme eD kg enc dec eK id F) Λ ε then 0 else 1) +
        chainBound (flatQ q k q) (flatQ (q + 4) k q) Λ ε (Fintype.card Z : ℝ≥0∞)⁻¹
          (owTerm eD kg enc dec eK hpk eG eJ eKR eC eKa A true)
          (owTerm eD kg enc dec eK hpk eG eJ eKR eC eKa A false) :=
  (avg_qINDCCAF_le hpk eG eJ eKR eC eKa (fun F => prfScheme eD kg enc dec eK id F) A Λ ε).trans
    (add_le_add le_rfl (chainBound_mono _ _ _ _ _
      (avg_qOwcpaAux_le_owTerm eD kg enc dec eK hpk eG eJ eKR eC eKa A true)
      (avg_qOwcpaAux_le_owTerm eD kg enc dec eK hpk eG eJ eKR eC eKa A false)))

end PRF

end CatCrypt.Crypto.MLKEM.PRFKEMChain

end

end
