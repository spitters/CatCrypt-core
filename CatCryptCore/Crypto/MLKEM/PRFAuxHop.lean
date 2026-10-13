/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.PRFOracle

/-!
# The `PRF_η` hop in the IND-CPA game with the auxiliary oracles

The IND-CPA game with oracle access of `Quantum/QROM/QIndcpaAux.lean` hands the
adversary the merged oracle `auxOracle`, which on the public-key slice of the
`G`-table encrypts under the coin of the table value. For the K-PKE whose noise
is read from the rows of a random table `F` (`prfScheme F`), this module
extends that oracle by `F` itself as a third summand of the domain and bounds
the distance between the IND-CPA experiment of `prfScheme F`, with `F` uniform,
and the experiment in which the key-generation and challenge noise are fresh
uniform rows while the oracle keeps reading `F`.

## Main definitions

* `prfScheme eD kg enc dec eK eE F` — the scheme with key generation at uniform
  public coins `φ` and a uniform seed `σ`, key noise the row of `F` at `σ`, and
  encryption noise the row of `F` at the coin
* `auxOracleF` — `auxOracle` of `prfScheme F` merged with `F`
* `auxRd` — the seed whose row the oracle answer at a point reads
* `QIndAuxPrfAdv` — an adversary: two messages from the public key and its coins,
  and from the public key, the challenge ciphertext, the key table `Hq` and its
  coins, an adversary on the extended oracle with a pure initial state
* `qIndAuxPrfPr`, `qIndAuxIdealPr` — the two experiments

## Main results

* `auxOracleF_local` — the answer of `auxOracleF` at a point depends on `F` only
  through the row named by `auxRd`
* `absDiff_qIndAuxPrfPr_qIndAuxIdealPr` — the two experiments differ by at most
  `|Sd|⁻¹ + 4 √(q · 8 q |Sd|⁻¹)`
* `qIndAuxPrf_adv_le` — the IND-CPA advantages differ by at most twice that
* `not_hcoin_prfScheme` — when some noise row makes a message fail under the key
  pair it generates, the table whose every row is that row has no correctly
  decrypting coin for the message: the coin hypothesis of the KEM bound does not
  hold at every table

## The model

The program of a `QIndAuxPrfAdv` is a `QAdv` with a fixed number `q` of queries
to `auxOracleF`.
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.QROM
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Crypto.MLKEM.PRFAuxHop

open CatCrypt.Crypto.MLKEM.PRFOracle

/-! ## The scheme with noise from the table -/

section Scheme

variable {Sd Nc PK SK M C KS R Φ : Type} {m₃ n : ℕ} [Fintype Φ] [Nonempty Φ] [Fintype Sd]
  [Nonempty Sd]
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → PK × SK) (enc : PK → M → R → C)
  (dec : SK → C → Option M) (eK : (Nc → Fin n) → KS) (eE : (Nc → Fin n) → R)

/-- The K-PKE with noise from the table `F`: key generation draws public coins
`φ` and a seed `σ` uniformly and returns `keygenPrf eD kg eK F φ σ`; encryption
with the coin `r` is `encPrf eD enc eE F`; decryption is `dec`. -/
def prfScheme (F : Fin m₃ → Fin n) : Scheme PK SK M C Sd where
  keygen := (PMF.uniformOfFintype (Φ × Sd)).map fun p => keygenPrf eD kg eK F p.1 p.2
  enc := encPrf eD enc eE F
  dec := dec

/-- **The coin hypothesis fails at a degenerate table.** If the key pair
generated from the noise row `ν` at the public coins `φ` does not decrypt the
encryption of `m` under the noise row `ν`, then at the table whose every row is
`ν` the key pair is generated and no coin decrypts the encryption of `m`. -/
theorem not_hcoin_prfScheme (φ : Φ) (ν : Nc → Fin n) (m : M)
    (hfail : dec (kg φ (eK ν)).2 (enc (kg φ (eK ν)).1 m (eE ν)) ≠ some m) :
    ¬ ∀ pk sk, (prfScheme eD kg enc dec eK eE (fun x => ν (eD.symm x).2)).keygen (pk, sk) ≠ 0 →
      ∀ m', ∃ ρ, (prfScheme eD kg enc dec eK eE (fun x => ν (eD.symm x).2)).dec sk
        ((prfScheme eD kg enc dec eK eE (fun x => ν (eD.symm x).2)).enc pk m' ρ) = some m' := by
  have hrow : ∀ s : Sd, prfRow eD (fun x => ν (eD.symm x).2) s = ν := fun s => by
    funext N
    simp [prfRow]
  intro h
  obtain ⟨σ⟩ := (inferInstance : Nonempty Sd)
  have hmem : (prfScheme eD kg enc dec eK eE (fun x => ν (eD.symm x).2)).keygen
      (kg φ (eK ν)) ≠ 0 := by
    rw [← PMF.mem_support_iff]
    refine (PMF.mem_support_map_iff _ _ _).mpr ⟨(φ, σ), by simp, ?_⟩
    simp [keygenPrf, hrow]
  obtain ⟨ρ, hρ⟩ := h _ _ hmem m
  exact hfail (by simpa [prfScheme, encPrf, hrow] using hρ)

end Scheme

/-! ## The oracle extended by the table -/

section Oracle

variable {Sd Nc PK SK M C KS K Hash Z Φ : Type} {m₁ m₂ m₃ n : ℕ} [Fintype Φ] [Nonempty Φ]
  [Fintype Sd] [Nonempty Sd] [DecidableEq Z] [DecidableEq Hash]
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → PK × SK) (enc : PK → M → (Nc → Fin n) → C)
  (dec : SK → C → Option M) (eK : (Nc → Fin n) → KS)
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × Sd) ≃ Fin n)

/-- The merged oracle `auxOracle` of `prfScheme F` on the first summand and the
table `F` on the second. -/
def auxOracleF (F : Fin m₃ → Fin n) (pk : PK) (Hq : C → K) (G : Fin m₁ → Fin n)
    (J : Fin m₂ → Fin n) (T : C → Fin n) (z : Z) : Fin ((m₁ + m₂) + m₃) → Fin n :=
  mergeOracle (auxOracle (prfScheme eD kg enc dec eK id F) hpk eG eJ eKR pk Hq G J T z) F

/-- The seed whose row of `F` the answer of `auxOracleF` reads: the coin of the
`G`-value on the public-key slice, the seed of the point on the `F`-summand, and
none elsewhere. -/
def auxRd (pk : PK) (G : Fin m₁ → Fin n) : Fin ((m₁ + m₂) + m₃) → Option Sd :=
  Fin.addCases
    (Fin.addCases (fun y => if kemSlice hpk eG pk y then some (eKR.symm (G y)).2 else none)
      fun _ => none)
    fun s => some (eD.symm s).1

/-- The answer of `auxOracleF` at a point depends on `F` only through the row at
the seed named by `auxRd`. -/
theorem auxOracleF_local (pk : PK) (Hq : C → K) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n)
    (T : C → Fin n) (z : Z) (F F' : Fin m₃ → Fin n) (t : Fin ((m₁ + m₂) + m₃))
    (h : ∀ s, auxRd eD hpk eG eKR pk G t = some s → prfRow eD F s = prfRow eD F' s) :
    auxOracleF eD kg enc dec eK hpk eG eJ eKR F pk Hq G J T z t =
      auxOracleF eD kg enc dec eK hpk eG eJ eKR F' pk Hq G J T z t := by
  induction t using Fin.addCases with
  | left u =>
    induction u using Fin.addCases with
    | left y =>
      by_cases hs : kemSlice hpk eG pk y
      · have hr := h (eKR.symm (G y)).2 (by simp [auxRd, hs])
        simp only [auxOracleF, auxOracle, mergeOracle_castAdd, keyHop, coinCt, kemEncAt,
          prfScheme, encPrf, if_pos hs, hr]
      · simp only [auxOracleF, auxOracle, mergeOracle_castAdd, keyHop, if_neg hs]
    | right y => simp only [auxOracleF, auxOracle, mergeOracle_castAdd, mergeOracle_natAdd]
  | right s =>
    have hr := congrFun (h (eD.symm s).1 (by simp [auxRd])) (eD.symm s).2
    simpa [auxOracleF, prfRow] using hr

end Oracle

/-! ## The two experiments -/

section Game

variable {Sd Nc PK SK M C KS K Hash Z Φ ι : Type} {m₁ m₂ m₃ n w q : ℕ}

/-- An IND-CPA adversary with coins in `ι` against the extended oracle: two
messages from the public key and its coins, and from the public key, the
challenge ciphertext, the key table `Hq` and its coins, an adversary on the
domain `(m₁ + m₂) + m₃` with a pure initial state. -/
structure QIndAuxPrfAdv (ι : Type) (m₁ m₂ m₃ n w q : ℕ) (PK C K M : Type) where
  /-- The two messages. -/
  msgs : PK → ι → M × M
  /-- The adversary run on the public key, the challenge ciphertext and `Hq`. -/
  prog : PK → C → (C → K) → ι → QAdv ((m₁ + m₂) + m₃) n w q
  /-- Every run starts from a pure state. -/
  pure : ∀ pk c h i, ∃ ψ : Fin (((m₁ + m₂) + m₃) * n * w) → ℂ,
    (prog pk c h i).init.val = vecMulVec ψ (star ψ)

/-- The message of `B` selected by the challenge bit `b`. -/
def QIndAuxPrfAdv.msg (B : QIndAuxPrfAdv ι m₁ m₂ m₃ n w q PK C K M) (pk : PK) (i : ι)
    (b : Bool) : M :=
  if b then (B.msgs pk i).2 else (B.msgs pk i).1

variable [Fintype Φ] [Nonempty Φ] [Fintype Sd] [DecidableEq Sd] [Nonempty Sd] [Fintype Nc]
  [DecidableEq Nc] [Fintype ι] [Nonempty ι] [Fintype Z] [Nonempty Z] [DecidableEq Z]
  [Fintype C] [DecidableEq C] [Fintype K] [Nonempty K] [DecidableEq Hash] [NeZero n]
  (eD : (Sd × Nc) ≃ Fin m₃) (kg : Φ → KS → PK × SK) (enc : PK → M → (Nc → Fin n) → C)
  (dec : SK → C → Option M) (eK : (Nc → Fin n) → KS)
  (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × Sd) ≃ Fin n)

/-- The side information of the experiments: public coins, adversary coins,
rejection seed and the tables `G`, `J`, `Hq`, `T`. -/
abbrev AuxSide (Φ ι Z C K : Type) (m₁ m₂ n : ℕ) : Type :=
  Φ × ι × Z × (Fin m₁ → Fin n) × (Fin m₂ → Fin n) × (C → K) × (C → Fin n)

/-- The public key and challenge ciphertext at the side information `ω`, the key
noise row `a` and the challenge noise row `b'`. -/
def auxView (B : QIndAuxPrfAdv ι m₁ m₂ m₃ n w q PK C K M) (b : Bool)
    (ω : AuxSide Φ ι Z C K m₁ m₂ n) (a b' : Nc → Fin n) : PK × C :=
  ((kg ω.1 (eK a)).1, enc (kg ω.1 (eK a)).1 (B.msg (kg ω.1 (eK a)).1 ω.2.1 b) b')

/-- The probability that `B` outputs `1` in the IND-CPA experiment of
`prfScheme F` with the challenge bit `b`: the side information, the seeds
`(σ, r)` and the table `F` uniform; the public key generated from the row at
`σ`, the challenge encrypted under the row at `r`, and `B` querying
`auxOracleF`. -/
def qIndAuxPrfPr (B : QIndAuxPrfAdv ι m₁ m₂ m₃ n w q PK C K M) (b : Bool) : ℝ≥0∞ :=
  avg fun ω : AuxSide Φ ι Z C K m₁ m₂ n => avg fun sr : Sd × Sd =>
    avg fun F : Fin m₃ → Fin n =>
      prOut (B.prog (auxView kg enc eK B b ω (prfRow eD F sr.1) (prfRow eD F sr.2)).1
          (auxView kg enc eK B b ω (prfRow eD F sr.1) (prfRow eD F sr.2)).2 ω.2.2.2.2.2.1 ω.2.1)
        (auxOracleF eD kg enc dec eK hpk eG eJ eKR F
          (auxView kg enc eK B b ω (prfRow eD F sr.1) (prfRow eD F sr.2)).1 ω.2.2.2.2.2.1
          ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.2 ω.2.2.1)

/-- The probability that `B` outputs `1` in the experiment whose key noise `a`
and challenge noise `b'` are uniform rows independent of the table `F` that
`auxOracleF` reads. -/
def qIndAuxIdealPr (B : QIndAuxPrfAdv ι m₁ m₂ m₃ n w q PK C K M) (b : Bool) : ℝ≥0∞ :=
  avg fun ω : AuxSide Φ ι Z C K m₁ m₂ n =>
    avg fun p : (Nc → Fin n) × (Nc → Fin n) × (Fin m₃ → Fin n) =>
      prOut (B.prog (auxView kg enc eK B b ω p.1 p.2.1).1 (auxView kg enc eK B b ω p.1 p.2.1).2
          ω.2.2.2.2.2.1 ω.2.1)
        (auxOracleF eD kg enc dec eK hpk eG eJ eKR p.2.2 (auxView kg enc eK B b ω p.1 p.2.1).1
          ω.2.2.2.2.2.1 ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.2 ω.2.2.1)

/-- **`PRF_η` as a quantum random oracle in the IND-CPA game with the auxiliary
oracles.** The experiment of `prfScheme F` and the experiment with uniform noise
rows differ by at most `|Sd|⁻¹ + 4 √(q · 8 q |Sd|⁻¹)`. -/
theorem absDiff_qIndAuxPrfPr_qIndAuxIdealPr (B : QIndAuxPrfAdv ι m₁ m₂ m₃ n w q PK C K M)
    (b : Bool) :
    absDiff (qIndAuxPrfPr eD kg enc dec eK hpk eG eJ eKR B b)
        (qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR B b) ≤
      (Fintype.card Sd : ℝ≥0∞)⁻¹ +
        4 * ((q : ℝ≥0∞) * (8 * q * (Fintype.card Sd : ℝ≥0∞)⁻¹)) ^ (1 / 2 : ℝ) := by
  have hwt : ∑ _ω : AuxSide Φ ι Z C K m₁ m₂ n,
      (Fintype.card (AuxSide Φ ι Z C K m₁ m₂ n) : ℝ≥0∞)⁻¹ = 1 := by
    simpa using sum_inv_mul_const (α := AuxSide Φ ι Z C K m₁ m₂ n) (1 : ℝ≥0∞)
  exact absDiff_prfReal_prfIdeal eD
    (fun _ : AuxSide Φ ι Z C K m₁ m₂ n => (Fintype.card (AuxSide Φ ι Z C K m₁ m₂ n) : ℝ≥0∞)⁻¹)
    (auxView kg enc eK B b) (fun ω x => B.prog x.1 x.2 ω.2.2.2.2.2.1 ω.2.1)
    (fun ω x F => auxOracleF eD kg enc dec eK hpk eG eJ eKR F x.1 ω.2.2.2.2.2.1 ω.2.2.2.1
      ω.2.2.2.2.1 ω.2.2.2.2.2.2 ω.2.2.1)
    (fun ω x => auxRd eD hpk eG eKR x.1 ω.2.2.2.1) hwt
    (fun ω x F F' t h => auxOracleF_local eD kg enc dec eK hpk eG eJ eKR x.1 _ _ _ _ _ F F' t h)
    (fun ω x => B.pure x.1 x.2 _ _)

/-- The IND-CPA advantage of `B` in the experiment of `prfScheme F` is at most its
advantage in the experiment with uniform noise rows, plus twice
`|Sd|⁻¹ + 4 √(q · 8 q |Sd|⁻¹)`. -/
theorem qIndAuxPrf_adv_le (B : QIndAuxPrfAdv ι m₁ m₂ m₃ n w q PK C K M) :
    absDiff (qIndAuxPrfPr eD kg enc dec eK hpk eG eJ eKR B true)
        (qIndAuxPrfPr eD kg enc dec eK hpk eG eJ eKR B false) ≤
      absDiff (qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR B true)
          (qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR B false) +
        2 * ((Fintype.card Sd : ℝ≥0∞)⁻¹ +
          4 * ((q : ℝ≥0∞) * (8 * q * (Fintype.card Sd : ℝ≥0∞)⁻¹)) ^ (1 / 2 : ℝ)) := by
  have h1 := absDiff_qIndAuxPrfPr_qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR B true
  have h0 := absDiff_qIndAuxPrfPr_qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR B false
  rw [absDiff_comm (qIndAuxPrfPr eD kg enc dec eK hpk eG eJ eKR B false)] at h0
  calc _ ≤ absDiff (qIndAuxPrfPr eD kg enc dec eK hpk eG eJ eKR B true)
          (qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR B true) +
        (absDiff (qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR B true)
            (qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR B false) +
          absDiff (qIndAuxIdealPr eD kg enc dec eK hpk eG eJ eKR B false)
            (qIndAuxPrfPr eD kg enc dec eK hpk eG eJ eKR B false)) :=
        (absDiff_triangle _ _ _).trans (add_le_add le_rfl (absDiff_triangle _ _ _))
    _ ≤ _ := by
        calc _ ≤ _ + (_ + _) := add_le_add h1 (add_le_add le_rfl h0)
          _ = _ := by ring

end Game

end CatCrypt.Crypto.MLKEM.PRFAuxHop

end

end
