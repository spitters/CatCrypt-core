/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.MultiRound
public import CatCryptCore.Quantum.QROM.TTransformQROM
public import CatCryptCore.Crypto.KEM.FIPS203KEM

/-!
# The IND-CCA game of the FIPS 203 KEM against a quantum adversary

The U-step of the quantum-random-oracle proof of the Fujisaki–Okamoto
transform bounds the IND-CCA advantage against `fips203 P hpk` of an adversary
with quantum access to the two random oracles `G : M × Hash → K × R` and
`J : Z × C → K` and classical access to decapsulation. The adversary is a
`QAdvMR` of `Quantum/QROM/MultiRound.lean`: one quantum oracle function on a
tagged domain `Fin (m₁ + m₂)` carrying `G` on the first summand and `J` on the
second, and classical rounds whose function is decapsulation with the
challenge ciphertext excluded.

## Main definitions

* `mergeOracle g j` — the oracle `Fin (m₁ + m₂) → Fin n` that is `g` on
  `Fin.castAdd` and `j` on `Fin.natAdd`
* `decapsFixed P hpk g j dk c` — decapsulation of `fips203 P hpk` at the fixed
  oracle functions `g` and `j`, as a function
* `decapsOracle P hpk eC eKa g j dk cstar` — the classical function of the
  rounds: decapsulation on `Fin c`, answering `cstar` with a fixed value
* `winBitProj M n w` — the projector onto output bit `1` on the first factor of
  the work register `Fin (2 * w)`
* `KEMQAdv m₁ m₂ n w q k c a PK C K` — the adversary: a `QAdvMR` for each public
  key, challenge ciphertext and challenge key, with final projector `winBitProj`
  and a pure initial state
* `KEMInput`, `kemSample` — the game input `((pk, sk), z, m*, K_fake, G, J)` and
  its weight: `keygen` on the key pair, the rest uniform
* `kemG`, `kemJ`, `kemChal`, `kemKey` — the oracle functions, the challenge
  ciphertext and the challenge key at an input and a bit
* `prWinKEM P hpk eG eJ eKR eC eKa A b` — the probability that `A` outputs `1`
  in the game with bit `b`
* `qINDCCAAdvantage P hpk eG eJ eKR eC eKa A` — `|prWinKEM true − prWinKEM false|`

## Main results

* `mergeOracle_agree` — two merged oracles agree outside the union of the
  embedded punctured sets when the components agree outside each
* `decapsFixed_spec` — the decapsulation program of `fips203` at `fixedRO2 g j`
  returns `some (decapsFixed P hpk g j dk c)`
* `winBitProj_isProj` — `winBitProj` is an orthogonal projector
* `kemSample_sum` — the input weights sum to one
* `prTrue_Q_le_one`, `prOutMR_le_one`, `prWinKEM_le_one` — the probabilities are
  at most one

## The model

The game models quantum access to `G` and `J` through one oracle on the tagged
domain, classical decapsulation queries answered by `decapsFixed` on every
ciphertext other than the challenge, and one final output bit. The number of
rounds `k` and the queries per segment `q` are parameters of the adversary type
`KEMQAdv`. The oracle `J` is read through the range encoding
`eKR : K × R ≃ Fin n` and the first projection, so that a uniform table gives a
uniform key.

## The hops of the U-step

1. `Quantum/QROM/HopJPrefix.lean`: `J(z, ·)` is replaced by an independent
   table; the oracles agree outside `{z} × C` embedded by `Fin.natAdd`, and the
   `Find` probability is bounded by the probability of guessing `z`.
2. `Quantum/QROM/HopDecaps.lean`: decapsulation is answered from the `G`-table
   without the secret key, with the same answers on inputs whose `G`-table has
   no decryption failure.
3. `Quantum/QROM/HopChallengeKey.lean`: the `G`-table is reprogrammed at the
   challenge point `eG (m*, hpk pk)`, embedded by `Fin.castAdd`, and the
   challenge key becomes independent of the adversary's oracle.

## References

* NIST FIPS 203, *Module-Lattice-Based Key-Encapsulation Mechanism Standard*,
  Algorithms 16–18.
* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.2
* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], §3
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
open CatCrypt.Crypto (OracleAdv)
open CatCrypt.Crypto.PKE.Games (Scheme)
open CatCrypt.Crypto.KEM.FIPS203 (fips203 fixedRO2)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Merging two oracles on a tagged domain -/

section Merge

variable {m₁ m₂ n : ℕ}

/-- The oracle on `Fin (m₁ + m₂)` that is `g` on the first summand and `j` on
    the second. -/
def mergeOracle (g : Fin m₁ → Fin n) (j : Fin m₂ → Fin n) : Fin (m₁ + m₂) → Fin n :=
  Fin.addCases g j

@[simp]
theorem mergeOracle_castAdd (g : Fin m₁ → Fin n) (j : Fin m₂ → Fin n) (x : Fin m₁) :
    mergeOracle g j (Fin.castAdd m₂ x) = g x :=
  Fin.addCases_left x

@[simp]
theorem mergeOracle_natAdd (g : Fin m₁ → Fin n) (j : Fin m₂ → Fin n) (y : Fin m₂) :
    mergeOracle g j (Fin.natAdd m₁ y) = j y :=
  Fin.addCases_right y

/-- The punctured set of a merged oracle: `S₁` on the first summand and `S₂` on
    the second. -/
def mergeSet (S₁ : Finset (Fin m₁)) (S₂ : Finset (Fin m₂)) : Finset (Fin (m₁ + m₂)) :=
  S₁.map (Fin.castAddEmb m₂) ∪ S₂.map (Fin.natAddEmb m₁)

/-- Two merged oracles agree outside `mergeSet S₁ S₂` when the first components
    agree outside `S₁` and the second outside `S₂`. -/
theorem mergeOracle_agree {g g' : Fin m₁ → Fin n} {j j' : Fin m₂ → Fin n}
    {S₁ : Finset (Fin m₁)} {S₂ : Finset (Fin m₂)} (h₁ : ∀ x, x ∉ S₁ → g x = g' x)
    (h₂ : ∀ y, y ∉ S₂ → j y = j' y) :
    ∀ z, z ∉ mergeSet S₁ S₂ → mergeOracle g j z = mergeOracle g' j' z := by
  intro z hz
  induction z using Fin.addCases with
  | left x =>
    simp only [mergeOracle_castAdd]
    refine h₁ x fun hx => hz ?_
    exact Finset.mem_union_left _ (Finset.mem_map_of_mem _ hx)
  | right y =>
    simp only [mergeOracle_natAdd]
    refine h₂ y fun hy => hz ?_
    exact Finset.mem_union_right _ (Finset.mem_map_of_mem _ hy)

end Merge

/-! ## Decapsulation at fixed oracles -/

section Decaps

variable {PK SK M C R K Hash Z : Type} [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [Nonempty R] [Nonempty K] [DecidableEq C]

/-- Decapsulation of `fips203 P hpk` at the fixed oracle functions `g` and `j`,
    with decapsulation key `dk = (sk, pk, z)`: decrypt `c` to `m'`, return
    `(g (m', hpk pk)).1` when re-encryption gives `c`, and `j (z, c)` otherwise
    or when decryption rejects.

    References: NIST, FIPS 203, "Module-Lattice-Based Key-Encapsulation Mechanism
    Standard", 2024, Algorithms 17 and 18 (encapsulation and decapsulation with
    implicit rejection); Hofheinz, Hövelmanns, Kiltz, "A modular analysis of the
    Fujisaki-Okamoto transformation", TCC 2017, ePrint 2017/604 (the U⊥̸
    transform); Duman, Hövelmanns, Kiltz, Lyubashevsky, Seiler, "Faster
    lattice-based KEMs via a generic Fujisaki-Okamoto transform using prefix
    hashing", CCS 2021, ePrint 2021/1351 (the public-key hash `hpk pk` in the key
    derivation). -/
def decapsFixed (P : Scheme PK SK M C R) (hpk : PK → Hash) (g : M × Hash → K × R)
    (j : Z × C → K) (dk : SK × PK × Z) (c : C) : K :=
  match P.dec dk.1 c with
  | none => j (dk.2.2, c)
  | some m =>
    if P.enc dk.2.1 m (g (m, hpk dk.2.1)).2 = c then (g (m, hpk dk.2.1)).1 else j (dk.2.2, c)

/-- The decapsulation program of `fips203 P hpk` at `fixedRO2 g j` returns
    `some (decapsFixed P hpk g j dk c)`. -/
theorem decapsFixed_spec (P : Scheme PK SK M C R) (hpk : PK → Hash) (g : M × Hash → K × R)
    (j : Z × C → K) (dk : SK × PK × Z) (c : C) :
    OracleAdv.run (fixedRO2 g j) ((fips203 P hpk).decaps dk c) () =
      PMF.pure (some (decapsFixed P hpk g j dk c), ()) := by
  obtain ⟨sk, pk, z⟩ := dk
  simp only [fips203, decapsFixed]
  rcases hd : P.dec sk c with _ | m
  · simp [OracleAdv.run_bind]
  · by_cases he : P.enc pk m (g (m, hpk pk)).2 = c
    · simp [he, OracleAdv.run_bind]
    · simp [he, OracleAdv.run_bind]

variable {c a : ℕ}

/-- The classical function of the decapsulation rounds: on the encoded
    ciphertext `x`, the encoded key `decapsFixed P hpk g j dk (eC.symm x)`, except
    at the challenge `cstar`, which is answered by a fixed key. -/
def decapsOracle (P : Scheme PK SK M C R) (hpk : PK → Hash) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
    (g : M × Hash → K × R) (j : Z × C → K) (dk : SK × PK × Z) (cstar : C) : Fin c → Fin a :=
  fun x => if eC.symm x = cstar then eKa (Classical.arbitrary K)
    else eKa (decapsFixed P hpk g j dk (eC.symm x))

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] in
theorem decapsOracle_of_ne (P : Scheme PK SK M C R) (hpk : PK → Hash) (eC : C ≃ Fin c)
    (eKa : K ≃ Fin a) (g : M × Hash → K × R) (j : Z × C → K) (dk : SK × PK × Z) (cstar : C)
    (c' : C) (h : c' ≠ cstar) :
    decapsOracle P hpk eC eKa g j dk cstar (eC c') = eKa (decapsFixed P hpk g j dk c') := by
  simp [decapsOracle, h]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] in
theorem decapsOracle_cstar (P : Scheme PK SK M C R) (hpk : PK → Hash) (eC : C ≃ Fin c)
    (eKa : K ≃ Fin a) (g : M × Hash → K × R) (j : Z × C → K) (dk : SK × PK × Z) (cstar : C) :
    decapsOracle P hpk eC eKa g j dk cstar (eC cstar) = eKa (Classical.arbitrary K) := by
  simp [decapsOracle]

end Decaps

/-! ## The output projector -/

section WinBitProj

variable (M n w : ℕ)

/-- The projector `1 ⊗ |1⟩⟨1| ⊗ 1` onto the states whose work register
    `Fin (2 * w)` has first factor `1`, on the total register
    `Fin (M * n * (2 * w))`. -/
def winBitProj : Matrix (Fin (M * n * (2 * w))) (Fin (M * n * (2 * w))) ℂ :=
  (1 : Matrix (Fin (M * n)) (Fin (M * n)) ℂ) ⊗ₖ
    (Matrix.diagonal (indS 2 {1}) ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ))

theorem winBitProj_mul_self : winBitProj M n w * winBitProj M n w = winBitProj M n w := by
  unfold winBitProj
  rw [kronecker_mul_kronecker, kronecker_mul_kronecker, Matrix.one_mul, Matrix.one_mul,
    Matrix.diagonal_mul_diagonal]
  congr 3
  funext y
  exact indS_singleton_mul_self 2 1 y

theorem winBitProj_conjTranspose : (winBitProj M n w)ᴴ = winBitProj M n w := by
  unfold winBitProj
  rw [conjTranspose_kronecker, conjTranspose_kronecker, conjTranspose_one, conjTranspose_one,
    Matrix.diagonal_conjTranspose]
  congr 3
  funext y
  exact indS_singleton_star 2 1 y

/-- `winBitProj` is an orthogonal projector: idempotent and self-adjoint. -/
theorem winBitProj_isProj :
    winBitProj M n w * winBitProj M n w = winBitProj M n w ∧ (winBitProj M n w)ᴴ = winBitProj M n w :=
  ⟨winBitProj_mul_self M n w, winBitProj_conjTranspose M n w⟩

end WinBitProj

/-! ## The adversary -/

/-- A quantum IND-CCA adversary against the FIPS 203 KEM: on a public key, a
    challenge ciphertext and a challenge key, a multi-round adversary on the
    register `Fin ((m₁ + m₂) * n * (2 * w))` with `k` decapsulation rounds of
    alphabet `Fin c → Fin a`, whose final projector is `winBitProj` and whose
    initial state is pure. An adversary starting in a mixed state is covered
    through a purification on a larger work register, since the work dimension
    `w` is arbitrary; the equality of the two winning probabilities is not
    proved here.

    References: Boneh, Dagdelen, Fischlin, Lehmann, Schaffner, Zhandry, "Random
    oracles in a quantum world", ASIACRYPT 2011, ePrint 2010/428 (the quantum
    random-oracle model: oracle queries in superposition, decapsulation queries
    classical). -/
structure KEMQAdv (m₁ m₂ n w q k c a : ℕ) (PK C K : Type) where
  /-- The adversary at a public key, a challenge ciphertext and a challenge key. -/
  run : PK → C → K → QAdvMR (m₁ + m₂) n (2 * w) q k c a
  /-- The final projector is the projector onto output bit `1`. -/
  final_eq : ∀ pk c K, (run pk c K).final = winBitProj (m₁ + m₂) n w
  /-- The initial state is pure. -/
  pure : ∀ pk c K, ∃ ψ : Fin ((m₁ + m₂) * n * (2 * w)) → ℂ,
    (run pk c K).init.val = Matrix.vecMulVec ψ (star ψ)

/-! ## Probabilities are at most one -/

section LeOne

variable {d : ℕ}

/-- The trace of one branch of an instrument on a positive semidefinite input is
    at most the trace of the input. -/
theorem branch_trace_re_le {α : Type} (I : QComp d α) (b : α)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) :
    (I.branch b ρ).trace.re ≤ ρ.trace.re :=
  calc (I.branch b ρ).trace.re
      ≤ ∑' a, (I.branch a ρ).trace.re :=
        (trace_re_summable (I.branch_summable ρ)).le_tsum b
          (fun a _ => trace_re_nonneg_of_psd (I.branch_psd a ρ hρ))
    _ = (∑' a, (I.branch a ρ).trace).re :=
        (Complex.re_tsum (trace_summable (I.branch_summable ρ))).symm
    _ ≤ ρ.trace.re := I.branch_stp ρ hρ

/-- `prTrue_Q` is at most one. -/
theorem prTrue_Q_le_one (I : QComp d Bool) (ρ : DensityMatrix d) : prTrue_Q I ρ ≤ 1 := by
  unfold prTrue_Q
  have h := branch_trace_re_le I true ρ.val ρ.psd
  rw [ρ.tr_one, Complex.one_re] at h
  exact ENNReal.ofReal_le_one.mpr h

end LeOne

section MRLeOne

variable {m n w q k c a : ℕ} [NeZero n]

/-- The output probability of a multi-round adversary is at most one. -/
theorem prOutMR_le_one (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    prOutMR A H f ≤ 1 :=
  prTrue_Q_le_one _ _

end MRLeOne

/-! ## The game -/

section Game

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Fintype K] [Nonempty K] [Nonempty R]
  [DecidableEq C] (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

/-- The input of the KEM game: a key pair, the rejection seed, the challenge
    message, the fake key, and the two oracle tables. -/
abbrev KEMInput (PK SK Z M K : Type) (m₁ m₂ n : ℕ) : Type :=
  (PK × SK) × Z × M × K × (Fin m₁ → Fin n) × (Fin m₂ → Fin n)

/-- The weight of an input: the key pair under `keygen`; the seed, the message,
    the fake key and the two tables uniform. -/
def kemSample (i : KEMInput PK SK Z M K m₁ m₂ n) : ℝ≥0∞ :=
  P.keygen i.1 * (Fintype.card Z : ℝ≥0∞)⁻¹ * (Fintype.card M : ℝ≥0∞)⁻¹ *
    (Fintype.card K : ℝ≥0∞)⁻¹ * ((n : ℝ≥0∞) ^ m₁)⁻¹ * ((n : ℝ≥0∞) ^ m₂)⁻¹

omit [DecidableEq C] in
include eKR in
/-- The input weights sum to one. -/
theorem kemSample_sum : ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i = 1 := by
  have hn : n ≠ 0 := Nat.pos_iff_ne_zero.mp (eKR (Classical.arbitrary (K × R))).pos
  have hkey : ∑ ks, P.keygen ks = 1 := by
    have := P.keygen.tsum_coe; rwa [tsum_fintype] at this
  have hne : ∀ k : ℕ, k ≠ 0 → (k : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹ = 1 := fun k hk =>
    ENNReal.mul_inv_cancel (by exact_mod_cast hk) (ENNReal.natCast_ne_top k)
  have hpow : ∀ e : ℕ, ((n : ℝ≥0∞) ^ e) * ((n : ℝ≥0∞) ^ e)⁻¹ = 1 := fun e =>
    ENNReal.mul_inv_cancel (pow_ne_zero _ (by exact_mod_cast hn))
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
  calc ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i
      = (∑ ks, P.keygen ks) *
          ((Fintype.card Z : ℝ≥0∞) * (Fintype.card Z : ℝ≥0∞)⁻¹) *
          ((Fintype.card M : ℝ≥0∞) * (Fintype.card M : ℝ≥0∞)⁻¹) *
          ((Fintype.card K : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞)⁻¹) *
          (((n : ℝ≥0∞) ^ m₁) * ((n : ℝ≥0∞) ^ m₁)⁻¹) *
          (((n : ℝ≥0∞) ^ m₂) * ((n : ℝ≥0∞) ^ m₂)⁻¹) := by
        simp only [kemSample, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
          Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
          Nat.cast_pow]
        simp only [mul_assoc, Finset.sum_mul]
        exact Finset.sum_congr rfl fun pk _ => Finset.sum_congr rfl fun sk _ => by ring
    _ = 1 := by
        rw [hkey, hne _ Fintype.card_ne_zero, hne _ Fintype.card_ne_zero,
          hne _ Fintype.card_ne_zero, hpow, hpow]
        simp

/-- The oracle `G` at an input, read through the encodings. -/
def kemG (i : KEMInput PK SK Z M K m₁ m₂ n) : M × Hash → K × R :=
  fun x => eKR.symm (i.2.2.2.2.1 (eG x))

/-- The oracle `J` at an input: the table on the second summand read through
    `eKR` and projected to the key. -/
def kemJ (i : KEMInput PK SK Z M K m₁ m₂ n) : Z × C → K :=
  fun x => (eKR.symm (i.2.2.2.2.2 (eJ x))).1

/-- The challenge ciphertext at an input: `P.enc pk m* (G (m*, hpk pk)).2`. -/
def kemChal (i : KEMInput PK SK Z M K m₁ m₂ n) : C :=
  P.enc i.1.1 i.2.2.1 (kemG eG eKR i (i.2.2.1, hpk i.1.1)).2

/-- The challenge key at an input and a bit: the encapsulated key
    `(G (m*, hpk pk)).1` at `true` and the fake key at `false`. -/
def kemKey (i : KEMInput PK SK Z M K m₁ m₂ n) (b : Bool) : K :=
  if b then (kemG eG eKR i (i.2.2.1, hpk i.1.1)).1 else i.2.2.2.1

/-- The merged quantum oracle at an input. -/
def kemOracle (i : KEMInput PK SK Z M K m₁ m₂ n) : Fin (m₁ + m₂) → Fin n :=
  mergeOracle i.2.2.2.2.1 i.2.2.2.2.2

/-- The decapsulation function of the rounds at an input: `decapsFixed` with
    the key `(sk, pk, z)`, the challenge ciphertext excluded. -/
def kemDecaps (i : KEMInput PK SK Z M K m₁ m₂ n) : Fin c → Fin a :=
  decapsOracle P hpk eC eKa (kemG eG eKR i) (kemJ eJ eKR i) (i.1.2, i.1.1, i.2.1)
    (kemChal P hpk eG eKR i)

variable [NeZero n]

/-- The probability that `A` outputs `1` in the IND-CCA game with bit `b`: the
    input is drawn with weight `kemSample`, the adversary is run on `pk`, the
    challenge ciphertext and the challenge key, against the merged oracle and
    the decapsulation rounds. -/
def prWinKEM (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) : ℝ≥0∞ :=
  ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
    prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i) (kemKey hpk eG eKR i b)) (kemOracle i)
      (kemDecaps P hpk eG eJ eKR eC eKa i)

/-- The quantum IND-CCA advantage of `A` against `fips203 P hpk`.

    References: Boneh, Dagdelen, Fischlin, Lehmann, Schaffner, Zhandry, "Random
    oracles in a quantum world", ASIACRYPT 2011, ePrint 2010/428 (the IND-CCA
    game in the quantum random-oracle model). -/
def qINDCCAAdvantage (A : KEMQAdv m₁ m₂ n w q k c a PK C K) : ℝ≥0∞ :=
  absDiff (prWinKEM P hpk eG eJ eKR eC eKa A true) (prWinKEM P hpk eG eJ eKR eC eKa A false)

include eKR in
/-- The winning probability is at most one. -/
theorem prWinKEM_le_one (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinKEM P hpk eG eJ eKR eC eKa A b ≤ 1 := by
  calc prWinKEM P hpk eG eJ eKR eC eKa A b
      ≤ ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * 1 :=
        Finset.sum_le_sum fun i _ => by gcongr; exact prOutMR_le_one _ _ _
    _ = 1 := by simp only [mul_one]; exact kemSample_sum (Z := Z) (K := K) P eKR

end Game

end CatCrypt.Quantum.QROM
