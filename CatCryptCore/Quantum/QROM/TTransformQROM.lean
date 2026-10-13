/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.QAdvGame
public import CatCryptCore.Crypto.PKE.Games

/-!
# The T transform in the QROM: the one-way-to-hiding step

The T transform of Hofheinz–Hövelmanns–Kiltz (TCC 2017, §4.1) derandomises a
public-key encryption scheme `P` with a hash `G`: `T[P, G]` encrypts `m` with
the coins `G m`. Against a quantum adversary with superposition access to `G`,
the first step of Theorem 4.4 replaces `G` by the oracle `G'` reprogrammed at
the challenge message `m*` to an independent uniform value. The adversary can
tell the two games apart only by querying `m*`, which the one-way-to-hiding
bound of `Quantum/QROM/QAdvGame.lean` quantifies with the punctured set
`{m*}`; in the reprogrammed game the coins of the challenge ciphertext are
independent of the oracle the adversary queries.

The message space is encoded as `Fin m` and the coin space as `Fin n`, so the
oracle is a function `Fin m → Fin n` on the query register of
`Quantum/QROM/SemiClassicalOracle.lean`. The work register is `Fin (m * w)`:
its first factor carries the adversary's output message.

## Main definitions

* `winProj m n w x` — the projector onto output `x` on the first factor of the
  work register, `1 ⊗ |x⟩⟨x| ⊗ 1`
* `TAdv m n w q PK C` — a quantum OW-CPA adversary against the T transform: a
  `q`-query adversary for each public key, challenge ciphertext and target
  message, with final projector `winProj` at the target and a pure initial state
* `tSample`, `tGame` — the OW-CPA game of `T[P, G]` as a `QGame` over the input
  `((pk, sk), m*, r, G)` with the oracle `G`, the reprogrammed oracle
  `G[m* ↦ r]` and the punctured set `{m*}`
* `tOwAdvantage`, `tOwAdvantage'`, `tFind` — the winning probability against
  `G`, against the reprogrammed oracle, and the `Find` probability at `{m*}`
* `swapAt` — the involution `(r, G) ↦ (G m*, G[m* ↦ r])` on coins and oracles

## Main results

* `winProj_isProj` — `winProj` is an orthogonal projector
* `tSample_sum` — the input weights sum to one
* `tOw_le_reprogrammed_add_find` —
  `tOwAdvantage ≤ tOwAdvantage' + 4 √(q · tFind)`
* `tOwAdvantage'_eq` — the reprogrammed game is the OW-CPA game of `P` with
  fresh coins and an oracle independent of them

## Scope

The module gives the one-way-to-hiding step only. Bounding `tOwAdvantage'` by
the OW-CPA advantage of a quantum adversary against `P`, and `tFind` by the
OW-CPA advantage of the adversary that measures a random query, needs a quantum
OW-CPA game for `P` and the extraction of the found query, which `runSC` does
not return; both belong to the next module.

## References

* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.1, Theorem 4.4
* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], §3
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The output projector -/

section WinProj

variable (m n w : ℕ)

/-- The projector `1 ⊗ |x⟩⟨x| ⊗ 1` onto the states whose work register has
    first factor `x`, on the total register `Fin (m * n * (m * w))`. -/
def winProj (x : Fin m) : Matrix (Fin (m * n * (m * w))) (Fin (m * n * (m * w))) ℂ :=
  (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℂ) ⊗ₖ
    (Matrix.diagonal (indS m {x}) ⊗ₖ (1 : Matrix (Fin w) (Fin w) ℂ))

theorem indS_singleton_mul_self (x y : Fin m) : indS m {x} y * indS m {x} y = indS m {x} y := by
  simp only [indS]; split_ifs <;> simp

theorem indS_singleton_star (x y : Fin m) : star (indS m {x} y) = indS m {x} y := by
  simp only [indS]; split_ifs <;> simp

theorem winProj_mul_self (x : Fin m) : winProj m n w x * winProj m n w x = winProj m n w x := by
  unfold winProj
  rw [kronecker_mul_kronecker, kronecker_mul_kronecker, Matrix.one_mul, Matrix.one_mul,
    Matrix.diagonal_mul_diagonal]
  congr 3
  funext y
  exact indS_singleton_mul_self m x y

theorem winProj_conjTranspose (x : Fin m) : (winProj m n w x)ᴴ = winProj m n w x := by
  unfold winProj
  rw [conjTranspose_kronecker, conjTranspose_kronecker, conjTranspose_one, conjTranspose_one,
    Matrix.diagonal_conjTranspose]
  congr 3
  funext y
  exact indS_singleton_star m x y

/-- `winProj` is an orthogonal projector: idempotent and self-adjoint. -/
theorem winProj_isProj (x : Fin m) :
    winProj m n w x * winProj m n w x = winProj m n w x ∧
      (winProj m n w x)ᴴ = winProj m n w x :=
  ⟨winProj_mul_self m n w x, winProj_conjTranspose m n w x⟩

end WinProj

/-! ## The adversary -/

/-- A quantum OW-CPA adversary against the T transform: on a public key, a
    challenge ciphertext and a target message `x`, a `q`-query adversary on the
    register `Fin (m * n * (m * w))` whose final projector is `winProj x` and
    whose initial state is pure. -/
structure TAdv (m n w q : ℕ) (PK C : Type) where
  /-- The adversary at a public key, a challenge ciphertext and a target message. -/
  run : PK → C → Fin m → QAdv m n (m * w) q
  /-- The final projector is the projector onto the target message. -/
  final_eq : ∀ pk c x, (run pk c x).final = winProj m n w x
  /-- The initial state is pure. -/
  pure : ∀ pk c x, ∃ ψ : Fin (m * n * (m * w)) → ℂ,
    (run pk c x).init.val = Matrix.vecMulVec ψ (star ψ)

/-! ## The game -/

section Game

variable {m n w q : ℕ} {PK SK M C R : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype R]
  [Nonempty M] [Nonempty R] (P : Scheme PK SK M C R) (eM : M ≃ Fin m) (eR : R ≃ Fin n)

/-- The input of the T game: a key pair, the challenge message, the fresh coin
    and the oracle. -/
abbrev TInput (PK SK M R : Type) (m n : ℕ) : Type := (PK × SK) × M × R × (Fin m → Fin n)

/-- The weight of an input: the key pair under `keygen`, the message, the coin
    and the oracle uniform. -/
def tSample (i : TInput PK SK M R m n) : ℝ≥0∞ :=
  P.keygen i.1 * (Fintype.card M : ℝ≥0∞)⁻¹ * (Fintype.card R : ℝ≥0∞)⁻¹ *
    ((Fintype.card R : ℝ≥0∞) ^ Fintype.card M)⁻¹

include eM eR in
/-- The input weights sum to one. -/
theorem tSample_sum : ∑ i, tSample P (m := m) (n := n) i = 1 := by
  have hM : Fintype.card M = m := (Fintype.card_congr eM).trans (Fintype.card_fin m)
  have hR : Fintype.card R = n := (Fintype.card_congr eR).trans (Fintype.card_fin n)
  have hkey : ∑ ks, P.keygen ks = 1 := by
    have := P.keygen.tsum_coe; rwa [tsum_fintype] at this
  have hm : m ≠ 0 := hM ▸ Fintype.card_ne_zero
  have hn : n ≠ 0 := hR ▸ Fintype.card_ne_zero
  have hne : ∀ k : ℕ, k ≠ 0 → (k : ℝ≥0∞) * (k : ℝ≥0∞)⁻¹ = 1 := fun k hk =>
    ENNReal.mul_inv_cancel (by exact_mod_cast hk) (ENNReal.natCast_ne_top k)
  have hpow : ((n : ℝ≥0∞) ^ m) * ((n : ℝ≥0∞) ^ m)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (pow_ne_zero _ (by exact_mod_cast hn))
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
  calc ∑ i, tSample P (m := m) (n := n) i
      = (∑ ks, P.keygen ks) * ((m : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹) * ((n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) *
          (((n : ℝ≥0∞) ^ m) * ((n : ℝ≥0∞) ^ m)⁻¹) := by
        simp only [tSample, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
          Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, hM, hR,
          Nat.cast_mul, Nat.cast_pow]
        simp only [mul_assoc, Finset.sum_mul]
        exact Finset.sum_congr rfl fun pk _ => Finset.sum_congr rfl fun sk _ => by ring
    _ = 1 := by rw [hkey, hne _ hm, hne _ hn, hpow]; simp

/-- The T game as a `QGame`: at the input `((pk, sk), m*, r, G)` the adversary is
    run on `pk` and the challenge `enc pk m* (G m*)` with target `m*`, the oracle
    is `G`, the reprogrammed oracle is `G[m* ↦ r]`, and the punctured set is
    `{m*}`. -/
def tGame (A : TAdv m n w q PK C) : QGame m n (m * w) q (TInput PK SK M R m n) where
  sample := tSample P
  sample_sum := tSample_sum P eM eR
  adv i := A.run i.1.1 (P.enc i.1.1 i.2.1 (eR.symm (i.2.2.2 (eM i.2.1)))) (eM i.2.1)
  oracle i := i.2.2.2
  oracle' i := Function.update i.2.2.2 (eM i.2.1) (eR i.2.2.1)
  S i := {eM i.2.1}
  agree i x hx := (Function.update_of_ne (by simpa using hx) _ _).symm
  pure i := A.pure _ _ _

/-- The involution `(r, G) ↦ (G x, G[x ↦ r])` on coins and oracles. -/
def swapAt (x : Fin m) : R × (Fin m → Fin n) ≃ R × (Fin m → Fin n) where
  toFun p := (eR.symm (p.2 x), Function.update p.2 x (eR p.1))
  invFun p := (eR.symm (p.2 x), Function.update p.2 x (eR p.1))
  left_inv p := by simp
  right_inv p := by simp

omit [Nonempty R] in
/-- Summing over coins and oracles is invariant under `swapAt`. -/
theorem sum_swapAt (x : Fin m) (f : R → (Fin m → Fin n) → ℝ≥0∞) :
    ∑ r, ∑ G, f (eR.symm (G x)) (Function.update G x (eR r)) = ∑ r, ∑ G, f r G := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (swapAt eR x) _ _ (fun p => rfl)

variable [NeZero n]

/-- The OW-CPA winning probability of `A` against `T[P, G]` with a uniform
    quantum-accessible `G`. -/
def tOwAdvantage (A : TAdv m n w q PK C) : ℝ≥0∞ := prWin (tGame P eM eR A)

/-- The winning probability of `A` when the oracle is reprogrammed at the
    challenge message to an independent uniform coin. -/
def tOwAdvantage' (A : TAdv m n w q PK C) : ℝ≥0∞ := prWin' (tGame P eM eR A)

/-- The probability that the semi-classical oracle at `{m*}` finds a query. -/
def tFind (A : TAdv m n w q PK C) : ℝ≥0∞ := prFindAvg (tGame P eM eR A)

/-- The one-way-to-hiding step of Theorem 4.4 (Hofheinz–Hövelmanns–Kiltz, TCC
    2017): `tOwAdvantage ≤ tOwAdvantage' + 4 √(q · tFind)`. -/
theorem tOw_le_reprogrammed_add_find (A : TAdv m n w q PK C) :
    tOwAdvantage P eM eR A ≤
      tOwAdvantage' P eM eR A + 4 * ((q : ℝ≥0∞) * tFind P eM eR A) ^ (1 / 2 : ℝ) :=
  (absDiff_le_iff.mp (o2h_avg (tGame P eM eR A))).1

/-! ## The reprogrammed game as OW-CPA with an independent oracle -/

/-- The reprogrammed game is the OW-CPA game of `P` with fresh coins `r` and an
    oracle `G` independent of them: `tOwAdvantage'` is the average over
    `((pk, sk), m*, r, G)` of the winning probability of `A.run pk (enc pk m* r) m*`
    against `G`. -/
theorem tOwAdvantage'_eq (A : TAdv m n w q PK C) :
    tOwAdvantage' P eM eR A =
      ∑ i : TInput PK SK M R m n,
        tSample P i * prOut (A.run i.1.1 (P.enc i.1.1 i.2.1 i.2.2.1) (eM i.2.1)) i.2.2.2 := by
  simp only [tOwAdvantage', prWin', tGame, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun pk _ => Finset.sum_congr rfl fun sk _ =>
    Finset.sum_congr rfl fun x _ => ?_
  exact sum_swapAt eR (eM x)
    (fun r G => tSample P (((pk, sk), x, r, G) : TInput PK SK M R m n) *
      prOut (A.run pk (P.enc pk x r) (eM x)) G)

end Game

end CatCrypt.Quantum.QROM
