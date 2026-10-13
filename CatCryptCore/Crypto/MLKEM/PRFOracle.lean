/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.QIndcpaAux

/-!
# The noise function `PRF_η` as a quantum random oracle

FIPS 203 derives the encryption noise of K-PKE as `PRF_η(r, N)` over nonces `N`
from a 32-byte coin `r`, and the key-generation noise as `PRF_η(σ, N)` from a
secret 32-byte seed `σ`. This module models `PRF_η` as a random oracle
`F : Sd × Nc → Block`, encoded as a table `Fin m → Fin n`, and bounds the
distance between a quantum game in which the challenger reads the rows of `F`
at two secret uniform seeds and the adversary holds `F`, and the game in which
the two rows are replaced by fresh uniform rows.

## Main definitions

* `avg f` — the uniform average of `f` over a finite type
* `prfRow eD F s` — the row of `F` at the seed `s`: the values `F (s, N)`
* `setRows eD F s r a b` — `F` with its rows at `s` and `r` replaced by `a` and `b`
* `prfReal`, `prfIdeal` — the two games: an adversary with classical input
  `view ω a b` and oracle `Or ω (view ω a b) F`, with `(a, b)` the rows of `F` at
  two uniform seeds, or two uniform rows independent of `F`
* `rowPts rd ω x s` — the oracle points whose answer reads the row at `s`
* `encPrf`, `keygenPrf` — the encryption and key generation of a K-PKE whose
  noise is read from `F`
* `qIndPrfPr`, `qIndIdealPr` — the quantum IND-CPA experiments with the oracle `F`
  for the PRF scheme and for the scheme with uniform noise

## Main results

* `absDiff_prfReal_prfIdeal` — with `|Sd|` the number of seeds,
  `|prfReal - prfIdeal| ≤ |Sd|⁻¹ + 4 √(q · 8 q |Sd|⁻¹)`
* `absDiff_qIndPrfPr_qIndIdealPr` — the same bound between the IND-CPA
  experiments of the PRF scheme and of the scheme with uniform noise
* `qIndIdealPr_eq_uniform` — when the row assemblies push the uniform
  distribution to the uniform distribution, the second experiment is the IND-CPA
  experiment of the scheme with uniform key-generation seed and coins

## Scope

The oracle answer at a point may read at most one row of `F`, named by `rd`; the
hypothesis `hloc` of `absDiff_prfReal_prfIdeal` states that the answer depends on
`F` only through that row. The direct oracle `F` reads the row of its own seed;
a merged oracle that encrypts under coins read from another table reads the row
of those coins. The bound follows from the one-way-to-hiding lemma `o2h_avg` for
the tables `setRows eD F s r a b` and `F`, which agree outside the rows at `s`
and `r`, and the search bound `prFind_le_four_sum_guess`: the query register lies
in the rows of a seed independent of the adversary's view with probability at
most `|Sd|⁻¹`. The term `|Sd|⁻¹` is the probability that the two seeds coincide.
For FIPS 203, `Sd` is the 32-byte strings and `|Sd|⁻¹ = 2⁻²⁵⁶`. The oracle range
`Fin n` holds the longest `PRF_η` output; a shorter output is a prefix of it.

## References

* [Ambainis, Hamburg, Unruh — Quantum Security Proofs Using Semi-Classical
  Oracles, CRYPTO 2019], Theorems 1 and 2
* [NIST FIPS 203, Module-Lattice-Based Key-Encapsulation Mechanism Standard],
  Algorithms 13 and 14
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.QROM

noncomputable section

namespace CatCrypt.Crypto.MLKEM.PRFOracle

/-! ## Uniform averages -/

section Avg

variable {α β : Type} [Fintype α] [Fintype β]

/-- The uniform average of `f` over the finite type `α`. -/
def avg (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ x, (Fintype.card α : ℝ≥0∞)⁻¹ * f x

/-- `avg` is monotone. -/
theorem avg_mono {f g : α → ℝ≥0∞} (h : ∀ x, f x ≤ g x) : avg f ≤ avg g := by
  unfold avg
  gcongr with x
  exact h x

/-- The average of a constant is the constant. -/
theorem avg_const [Nonempty α] (c : ℝ≥0∞) : avg (fun _ : α => c) = c :=
  sum_inv_mul_const c

/-- An average of values at most one is at most one. -/
theorem avg_le_one [Nonempty α] {f : α → ℝ≥0∞} (h : ∀ x, f x ≤ 1) : avg f ≤ 1 :=
  (avg_mono h).trans (avg_const 1).le

/-- The average over a product is the iterated average. -/
theorem avg_prod (f : α × β → ℝ≥0∞) : avg f = avg fun x => avg fun y => f (x, y) := by
  unfold avg
  rw [Fintype.sum_prod_type, Fintype.card_prod, inv_natCast_mul]
  simp only [Finset.mul_sum, mul_assoc]

/-- Two iterated averages commute. -/
theorem avg_comm (f : α → β → ℝ≥0∞) :
    (avg fun x => avg fun y => f x y) = avg fun y => avg fun x => f x y := by
  unfold avg
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

/-- The average over a product of a function of the first component. -/
theorem avg_fst [Nonempty β] (f : α → ℝ≥0∞) : avg (fun p : α × β => f p.1) = avg f := by
  rw [avg_prod]
  simp only [avg_const]

/-- The average over a product of a function of the second component. -/
theorem avg_snd [Nonempty α] (f : β → ℝ≥0∞) : avg (fun p : α × β => f p.2) = avg f := by
  rw [avg_prod]
  exact avg_const (avg f)

/-- `avg` commutes with a constant factor. -/
theorem avg_mul_left (c : ℝ≥0∞) (f : α → ℝ≥0∞) : avg (fun x => c * f x) = c * avg f := by
  unfold avg
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `avg` is additive. -/
theorem avg_add (f g : α → ℝ≥0∞) : avg (fun x => f x + g x) = avg f + avg g := by
  simp only [avg, mul_add, Finset.sum_add_distrib]

/-- `avg` commutes with a finite sum. -/
theorem avg_sum {ι : Type} [Fintype ι] (f : ι → α → ℝ≥0∞) :
    avg (fun x => ∑ i, f i x) = ∑ i, avg (f i) := by
  simp only [avg, Finset.mul_sum]
  exact Finset.sum_comm

/-- `avg` is invariant under a permutation of its domain. -/
theorem avg_perm (e : Equiv.Perm α) (f : α → ℝ≥0∞) : avg (fun x => f (e x)) = avg f := by
  unfold avg
  exact Equiv.sum_comp e (fun x => (Fintype.card α : ℝ≥0∞)⁻¹ * f x)

/-- The average is `|α|⁻¹` times the sum. -/
theorem avg_eq_inv_mul_sum (f : α → ℝ≥0∞) :
    avg f = (Fintype.card α : ℝ≥0∞)⁻¹ * ∑ x, f x := by
  rw [avg, Finset.mul_sum]

/-- `absDiff` of two averages is at most the average of the `absDiff`s. -/
theorem absDiff_avg_le (f g : α → ℝ≥0∞) :
    absDiff (avg f) (avg g) ≤ avg fun x => absDiff (f x) (g x) :=
  (absDiff_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => absDiff_mul_left_le _ _ _)

/-- `absDiff` of two weighted sums is at most the weighted sum of the `absDiff`s. -/
theorem absDiff_wsum_le (wt : α → ℝ≥0∞) (f g : α → ℝ≥0∞) :
    absDiff (∑ x, wt x * f x) (∑ x, wt x * g x) ≤ ∑ x, wt x * absDiff (f x) (g x) :=
  (absDiff_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => absDiff_mul_left_le _ _ _)

/-- `absDiff` of two values at most one is at most one. -/
theorem absDiff_le_one {a b : ℝ≥0∞} (ha : a ≤ 1) (hb : b ≤ 1) : absDiff a b ≤ 1 :=
  max_le (tsub_le_self.trans ha) (tsub_le_self.trans hb)

/-- The average over pairs of the indicator of the diagonal is `|α|⁻¹`. -/
theorem avg_diag [DecidableEq α] [Nonempty α] :
    avg (fun p : α × α => if p.1 = p.2 then (1 : ℝ≥0∞) else 0) =
      (Fintype.card α : ℝ≥0∞)⁻¹ := by
  rw [avg_prod]
  unfold avg
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact sum_inv_mul_const _

end Avg

/-! ## Rows of the oracle table -/

section Rows

variable {Sd Nc : Type} {m n : ℕ} (eD : (Sd × Nc) ≃ Fin m)

/-- The row of the table `F` at the seed `s`: the values `F (s, N)` over the
nonces `N`. -/
def prfRow (F : Fin m → Fin n) (s : Sd) : Nc → Fin n := fun N => F (eD (s, N))

variable [DecidableEq Sd]

/-- The table `F` with its row at `s` replaced by `a` and its row at `r` replaced
by `b`; at `s = r` the row is `b`. -/
def setRows (F : Fin m → Fin n) (s r : Sd) (a b : Nc → Fin n) : Fin m → Fin n := fun x =>
  if (eD.symm x).1 = r then b (eD.symm x).2
  else if (eD.symm x).1 = s then a (eD.symm x).2 else F x

/-- The row at `r` of `setRows eD F s r a b` is `b`. -/
theorem prfRow_setRows_right (F : Fin m → Fin n) (s r : Sd) (a b : Nc → Fin n) :
    prfRow eD (setRows eD F s r a b) r = b := by
  funext N
  simp [prfRow, setRows]

/-- The row at `s` of `setRows eD F s r a b` is `a` when `s ≠ r`. -/
theorem prfRow_setRows_left (F : Fin m → Fin n) {s r : Sd} (h : s ≠ r) (a b : Nc → Fin n) :
    prfRow eD (setRows eD F s r a b) s = a := by
  funext N
  simp [prfRow, setRows, h]

/-- The rows of `setRows eD F s r a b` at seeds other than `s` and `r` are those
of `F`. -/
theorem prfRow_setRows_of_ne (F : Fin m → Fin n) {s r t : Sd} (hs : t ≠ s) (hr : t ≠ r)
    (a b : Nc → Fin n) : prfRow eD (setRows eD F s r a b) t = prfRow eD F t := by
  funext N
  simp [prfRow, setRows, hs, hr]

/-- Writing back the old rows at `s ≠ r` restores the table. -/
theorem setRows_prfRow (F : Fin m → Fin n) {s r : Sd} (h : s ≠ r) (a b : Nc → Fin n) :
    setRows eD (setRows eD F s r a b) s r (prfRow eD F s) (prfRow eD F r) = F := by
  funext x
  obtain ⟨⟨t, N⟩, rfl⟩ := eD.surjective x
  by_cases htr : t = r
  · subst htr
    simp [setRows, prfRow]
  · by_cases hts : t = s
    · subst hts
      simp [setRows, prfRow, htr]
    · simp [setRows, htr, hts]

/-- The exchange of two fresh rows with the rows of a table at `s` and `r`. -/
def rowSwap (s r : Sd) (p : (Nc → Fin n) × (Nc → Fin n) × (Fin m → Fin n)) :
    (Nc → Fin n) × (Nc → Fin n) × (Fin m → Fin n) :=
  (prfRow eD p.2.2 s, prfRow eD p.2.2 r, setRows eD p.2.2 s r p.1 p.2.1)

/-- `rowSwap` is an involution when `s ≠ r`. -/
theorem rowSwap_involutive {s r : Sd} (h : s ≠ r) :
    Function.Involutive (rowSwap (n := n) eD s r) := by
  rintro ⟨a, b, F⟩
  simp only [rowSwap, prfRow_setRows_left eD _ h, prfRow_setRows_right, setRows_prfRow eD _ h]

variable [Fintype Nc] [DecidableEq Nc] [NeZero n]

/-- At `s ≠ r`, reading two rows of a uniform table is the same as reading two
fresh uniform rows from the table in which they are written. -/
theorem avg_setRows {s r : Sd} (h : s ≠ r) (g : (Nc → Fin n) → (Nc → Fin n) → (Fin m → Fin n) → ℝ≥0∞) :
    (avg fun p : (Nc → Fin n) × (Nc → Fin n) × (Fin m → Fin n) =>
        g p.1 p.2.1 (setRows eD p.2.2 s r p.1 p.2.1)) =
      avg fun F : Fin m → Fin n => g (prfRow eD F s) (prfRow eD F r) F := by
  have hswap := avg_perm (rowSwap_involutive eD h).toPerm
    (fun p : (Nc → Fin n) × (Nc → Fin n) × (Fin m → Fin n) =>
      g (prfRow eD p.2.2 s) (prfRow eD p.2.2 r) p.2.2)
  simp only [Function.Involutive.coe_toPerm, rowSwap, prfRow_setRows_left eD _ h,
    prfRow_setRows_right] at hswap
  rw [hswap, avg_snd (fun q : (Nc → Fin n) × (Fin m → Fin n) =>
    g (prfRow eD q.2 s) (prfRow eD q.2 r) q.2)]
  exact avg_snd (fun F : Fin m → Fin n => g (prfRow eD F s) (prfRow eD F r) F)

end Rows

/-! ## The two games -/

section Game

variable {Ω X Sd Nc : Type} [Fintype Ω] [Fintype Sd] [DecidableEq Sd] [Nonempty Sd]
  [Fintype Nc] [DecidableEq Nc] {m M n w q : ℕ} [NeZero n]
  (eD : (Sd × Nc) ≃ Fin m) (wt : Ω → ℝ≥0∞)
  (view : Ω → (Nc → Fin n) → (Nc → Fin n) → X) (D : Ω → X → QAdv M n w q)
  (Or : Ω → X → (Fin m → Fin n) → Fin M → Fin n)

/-- The acceptance probability of the adversary at the side information `ω`, the
rows `a`, `b` and the table `F`: `D ω x` against `Or ω x F` with
`x = view ω a b`. -/
def prfRun (ω : Ω) (a b : Nc → Fin n) (F : Fin m → Fin n) : ℝ≥0∞ :=
  prOut (D ω (view ω a b)) (Or ω (view ω a b) F)

/-- The game in which the classical input is computed from the rows of the
oracle table `F` at two uniform seeds: the side information under `wt`, the seeds
`(s, r)` and the table `F` uniform. -/
def prfReal : ℝ≥0∞ :=
  ∑ ω, wt ω * avg fun sr : Sd × Sd => avg fun F : Fin m → Fin n =>
    prfRun view D Or ω (prfRow eD F sr.1) (prfRow eD F sr.2) F

/-- The game in which the classical input is computed from two uniform rows `a`,
`b` independent of the uniform oracle table `F`. -/
def prfIdeal : ℝ≥0∞ :=
  ∑ ω, wt ω * avg fun p : (Nc → Fin n) × (Nc → Fin n) × (Fin m → Fin n) =>
    prfRun view D Or ω p.1 p.2.1 p.2.2

/-- The intermediate game: the uniform rows `a`, `b` are written into the table
at the uniform seeds `(s, r)`. -/
def prfHyb : ℝ≥0∞ :=
  ∑ ω, wt ω * avg fun sr : Sd × Sd =>
    avg fun p : (Nc → Fin n) × (Nc → Fin n) × (Fin m → Fin n) =>
      prfRun view D Or ω p.1 p.2.1 (setRows eD p.2.2 sr.1 sr.2 p.1 p.2.1)

omit [Fintype Ω] [Fintype Nc] [DecidableEq Nc] in
/-- The acceptance probability `prfRun` is at most one. -/
theorem prfRun_le_one (ω : Ω) (a b : Nc → Fin n) (F : Fin m → Fin n) :
    prfRun view D Or ω a b F ≤ 1 :=
  prTrue_Q_le_one _ _

/-- The real and intermediate games differ by at most the probability `|Sd|⁻¹`
that the two seeds coincide. -/
theorem absDiff_prfReal_prfHyb (hwt : ∑ ω, wt ω = 1) :
    absDiff (prfReal eD wt view D Or) (prfHyb eD wt view D Or) ≤
      (Fintype.card Sd : ℝ≥0∞)⁻¹ := by
  unfold prfReal prfHyb
  refine (absDiff_wsum_le _ _ _).trans ?_
  calc _ ≤ ∑ ω, wt ω * (Fintype.card Sd : ℝ≥0∞)⁻¹ := by
        gcongr with ω
        refine (absDiff_avg_le _ _).trans ?_
        calc _ ≤ avg fun sr : Sd × Sd => if sr.1 = sr.2 then (1 : ℝ≥0∞) else 0 := by
              refine avg_mono fun sr => ?_
              by_cases h : sr.1 = sr.2
              · rw [if_pos h]
                exact absDiff_le_one (avg_le_one fun _ => prfRun_le_one _ _ _ _ _ _ _)
                  (avg_le_one fun _ => prfRun_le_one _ _ _ _ _ _ _)
              · rw [if_neg h, avg_setRows eD h
                  (fun a b F => prfRun view D Or ω a b F), absDiff_self]
          _ = _ := avg_diag
    _ = _ := by rw [← Finset.sum_mul, hwt, one_mul]

variable (rd : Ω → X → Fin M → Option Sd)

/-- The oracle points whose answer at `ω` and `x` reads the row at the seed `s`. -/
def rowPts (ω : Ω) (x : X) (s : Sd) : Finset (Fin M) :=
  Finset.univ.filter fun t => rd ω x t = some s

omit [Fintype Ω] [Fintype Sd] [DecidableEq Sd] [Nonempty Sd] [Fintype Nc] [DecidableEq Nc] in
/-- The guessing probabilities of the row sets over all seeds sum to at most
one. -/
theorem sum_guessProb_rowPts_le_one (A : QAdv M n w q) (H : Fin M → Fin n) (ω : Ω) (x : X)
    (j : Fin q) [Fintype Sd] [DecidableEq Sd] :
    ∑ s : Sd, guessProb A H (rowPts rd ω x s) j ≤ 1 := by
  have h := sum_prOut_queryPrefix_fiber_le_one A H j (rd ω x)
  rw [Fintype.sum_option] at h
  simp only [prOut_queryPrefix] at h
  exact le_add_self.trans h

omit [Fintype Ω] [Fintype Sd] [DecidableEq Sd] [Nonempty Sd] [Fintype Nc] [DecidableEq Nc]
  [NeZero n] in
/-- The guessing probability is subadditive in the set. -/
theorem guessProb_union_le [NeZero n] (A : QAdv M n w q) (H : Fin M → Fin n)
    (S T : Finset (Fin M)) (j : Fin q) {ψ : Fin (M * n * w) → ℂ}
    (hpure : A.init.val = vecMulVec ψ (star ψ)) :
    guessProb A H (S ∪ T) j ≤ guessProb A H S j + guessProb A H T j := by
  rw [guessProb_eq_sum A H _ j hpure, guessProb_eq_sum A H S j hpure,
    guessProb_eq_sum A H T j hpure, ← Finset.sum_union_inter]
  exact le_self_add

omit [Fintype Sd] [Nonempty Sd] [Fintype Nc] [DecidableEq Nc] [NeZero n] in
/-- The weighted sum over `Ω × β × γ` with uniform weights on `β` and `γ` is the
weighted sum over `Ω` of the iterated averages. -/
theorem sum_weight_eq {β γ : Type} [Fintype β] [Fintype γ] (f : Ω × β × γ → ℝ≥0∞) :
    ∑ i, wt i.1 * ((Fintype.card β : ℝ≥0∞)⁻¹ * (Fintype.card γ : ℝ≥0∞)⁻¹) * f i =
      ∑ ω, wt ω * avg fun b => avg fun c => f (ω, b, c) := by
  simp only [avg, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

variable {rd} in
omit [Fintype Ω] [Fintype Sd] [Nonempty Sd] [Fintype Nc] [DecidableEq Nc] [NeZero n] in
/-- Under `hloc`, the oracle at the table with the rows at `s` and `r` written
agrees with the oracle at the table outside the points that read those rows. -/
theorem or_setRows_agree
    (hloc : ∀ ω x F F' t, (∀ s, rd ω x t = some s → prfRow eD F s = prfRow eD F' s) →
      Or ω x F t = Or ω x F' t)
    (ω : Ω) (x : X) (F : Fin m → Fin n) (s r : Sd) (a b : Nc → Fin n) (t : Fin M)
    (ht : t ∉ rowPts rd ω x s ∪ rowPts rd ω x r) :
    Or ω x (setRows eD F s r a b) t = Or ω x F t := by
  refine hloc _ _ _ _ t fun s' hs' => ?_
  simp only [Finset.mem_union, rowPts, Finset.mem_filter, Finset.mem_univ, true_and,
    not_or] at ht
  refine prfRow_setRows_of_ne eD _ ?_ ?_ _ _
  · rintro rfl
    exact ht.1 hs'
  · rintro rfl
    exact ht.2 hs'

/-- The one-way-to-hiding game between the intermediate and the ideal game: at
the side information `ω`, the rows and table `p = (a, b, F)` and the seeds
`(s, r)`, the adversary `D ω (view ω a b)` runs against the oracle at the table
with the rows written at the seeds, or at the table itself; the punctured set is
the set of points that read the row at either seed. -/
def prfGame (hwt : ∑ ω, wt ω = 1)
    (hloc : ∀ ω x F F' t, (∀ s, rd ω x t = some s → prfRow eD F s = prfRow eD F' s) →
      Or ω x F t = Or ω x F' t)
    (hpure : ∀ ω x, ∃ ψ : Fin (M * n * w) → ℂ, (D ω x).init.val = vecMulVec ψ (star ψ)) :
    QGame M n w q (Ω × ((Nc → Fin n) × (Nc → Fin n) × (Fin m → Fin n)) × (Sd × Sd)) where
  sample i := wt i.1 *
    ((Fintype.card ((Nc → Fin n) × (Nc → Fin n) × (Fin m → Fin n)) : ℝ≥0∞)⁻¹ *
      (Fintype.card (Sd × Sd) : ℝ≥0∞)⁻¹)
  sample_sum := by
    have h := sum_weight_eq wt
      (fun _ : Ω × ((Nc → Fin n) × (Nc → Fin n) × (Fin m → Fin n)) × (Sd × Sd) =>
        (1 : ℝ≥0∞))
    simp only [mul_one, avg_const] at h
    exact h.trans hwt
  adv i := D i.1 (view i.1 i.2.1.1 i.2.1.2.1)
  oracle i := Or i.1 (view i.1 i.2.1.1 i.2.1.2.1)
    (setRows eD i.2.1.2.2 i.2.2.1 i.2.2.2 i.2.1.1 i.2.1.2.1)
  oracle' i := Or i.1 (view i.1 i.2.1.1 i.2.1.2.1) i.2.1.2.2
  S i := rowPts rd i.1 (view i.1 i.2.1.1 i.2.1.2.1) i.2.2.1 ∪
    rowPts rd i.1 (view i.1 i.2.1.1 i.2.1.2.1) i.2.2.2
  agree i t ht := or_setRows_agree eD Or hloc _ _ _ _ _ _ _ t ht
  pure i := hpure _ _

variable (hwt : ∑ ω, wt ω = 1)
  (hloc : ∀ ω x F F' t, (∀ s, rd ω x t = some s → prfRow eD F s = prfRow eD F' s) →
    Or ω x F t = Or ω x F' t)
  (hpure : ∀ ω x, ∃ ψ : Fin (M * n * w) → ℂ, (D ω x).init.val = vecMulVec ψ (star ψ))

/-- The game `prfGame` against the table with the rows written is the
intermediate game. -/
theorem prWin_prfGame :
    prWin (prfGame eD wt view D Or rd hwt hloc hpure) = prfHyb eD wt view D Or := by
  unfold prWin prfHyb
  refine (sum_weight_eq wt _).trans (Finset.sum_congr rfl fun ω _ => ?_)
  rw [avg_comm]
  rfl

/-- The game `prfGame` against the table itself is the ideal game. -/
theorem prWin'_prfGame :
    prWin' (prfGame eD wt view D Or rd hwt hloc hpure) = prfIdeal wt view D Or := by
  unfold prWin' prfIdeal
  refine (sum_weight_eq wt _).trans (Finset.sum_congr rfl fun ω _ => ?_)
  congr 1
  exact congrArg avg (funext fun p => avg_const (prfRun view D Or ω p.1 p.2.1 p.2.2))

include hloc hpure in
omit [Fintype Ω] [Fintype Nc] [DecidableEq Nc] in
/-- At fixed side information, rows and table, the `Find` probability averaged
over the two seeds is at most `8 q |Sd|⁻¹`. -/
theorem avg_prFind_seeds_le (ω : Ω) (a b : Nc → Fin n) (F : Fin m → Fin n) :
    (avg fun sr : Sd × Sd => prFind (D ω (view ω a b))
        (Or ω (view ω a b) (setRows eD F sr.1 sr.2 a b))
        (rowPts rd ω (view ω a b) sr.1 ∪ rowPts rd ω (view ω a b) sr.2)) ≤
      8 * q * (Fintype.card Sd : ℝ≥0∞)⁻¹ := by
  obtain ⟨ψ, hψ⟩ := hpure ω (view ω a b)
  set g : Sd → Fin q → ℝ≥0∞ := fun s j =>
    guessProb (D ω (view ω a b)) (Or ω (view ω a b) F) (rowPts rd ω (view ω a b) s) j with hg
  have hpt : ∀ sr : Sd × Sd, prFind (D ω (view ω a b))
        (Or ω (view ω a b) (setRows eD F sr.1 sr.2 a b))
        (rowPts rd ω (view ω a b) sr.1 ∪ rowPts rd ω (view ω a b) sr.2) ≤
      4 * ∑ j, (g sr.1 j + g sr.2 j) := by
    intro sr
    rw [prFind_congr _ _ _ _ (or_setRows_agree eD Or hloc ω _ F sr.1 sr.2 a b) hψ]
    refine (prFind_le_four_sum_guess _ _ _ hψ).trans ?_
    gcongr with j
    exact guessProb_union_le _ _ _ _ j hψ
  have hs : ∀ j, avg (fun s => g s j) ≤ (Fintype.card Sd : ℝ≥0∞)⁻¹ := fun j => by
    rw [avg_eq_inv_mul_sum]
    calc _ ≤ (Fintype.card Sd : ℝ≥0∞)⁻¹ * 1 := by
          gcongr
          exact sum_guessProb_rowPts_le_one rd _ _ ω _ j
      _ = _ := mul_one _
  calc _ ≤ avg fun sr : Sd × Sd => 4 * ∑ j, (g sr.1 j + g sr.2 j) := avg_mono hpt
    _ = 4 * ∑ j, (avg (fun s => g s j) + avg (fun s => g s j)) := by
        rw [avg_mul_left, avg_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [avg_add, avg_fst (fun s => g s j), avg_snd (fun s => g s j)]
    _ ≤ 4 * ∑ _j : Fin q, ((Fintype.card Sd : ℝ≥0∞)⁻¹ + (Fintype.card Sd : ℝ≥0∞)⁻¹) := by
        gcongr with j
        · exact hs j
        · exact hs j
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The averaged `Find` probability of `prfGame` is at most `8 q |Sd|⁻¹`. -/
theorem prFindAvg_prfGame_le :
    prFindAvg (prfGame eD wt view D Or rd hwt hloc hpure) ≤
      8 * q * (Fintype.card Sd : ℝ≥0∞)⁻¹ := by
  unfold prFindAvg
  refine (sum_weight_eq wt _).trans_le ?_
  calc _ ≤ ∑ ω, wt ω * (8 * q * (Fintype.card Sd : ℝ≥0∞)⁻¹) := by
        gcongr with ω
        refine (avg_mono fun p => ?_).trans (avg_const _).le
        exact avg_prFind_seeds_le eD view D Or rd hloc hpure ω p.1 p.2.1 p.2.2
    _ = _ := by rw [← Finset.sum_mul, hwt, one_mul]

include hwt hloc hpure in
/-- **`PRF_η` as a quantum random oracle.** An adversary whose classical input is
computed from the rows of the oracle table `F` at two secret uniform seeds, and
which holds an oracle reading at most one row of `F` per point, accepts with a
probability within `|Sd|⁻¹ + 4 √(q · 8 q |Sd|⁻¹)` of the probability in the game
where the two rows are uniform and independent of `F`. -/
theorem absDiff_prfReal_prfIdeal :
    absDiff (prfReal eD wt view D Or) (prfIdeal wt view D Or) ≤
      (Fintype.card Sd : ℝ≥0∞)⁻¹ +
        4 * ((q : ℝ≥0∞) * (8 * q * (Fintype.card Sd : ℝ≥0∞)⁻¹)) ^ (1 / 2 : ℝ) := by
  set G := prfGame eD wt view D Or rd hwt hloc hpure
  refine (absDiff_triangle _ (prfHyb eD wt view D Or) _).trans (add_le_add
    (absDiff_prfReal_prfHyb eD wt view D Or hwt) ?_)
  rw [← prWin_prfGame eD wt view D Or rd hwt hloc hpure,
    ← prWin'_prfGame eD wt view D Or rd hwt hloc hpure]
  refine (o2h_avg G).trans ?_
  gcongr
  exact prFindAvg_prfGame_le eD wt view D Or rd hwt hloc hpure

end Game

/-! ## The K-PKE with noise from the oracle -/

section PKE

variable {Sd Nc PK SK M C R KS Φ ι : Type} {m n w q : ℕ}
  (eD : (Sd × Nc) ≃ Fin m) (kg : Φ → KS → PK × SK) (enc : PK → M → R → C)
  (eK : (Nc → Fin n) → KS) (eE : (Nc → Fin n) → R)

/-- Key generation with noise from the oracle table `F`: the key pair of `kg` at
the public coins `φ` and the key-generation seed assembled by `eK` from the row
of `F` at the secret seed `σ`. -/
def keygenPrf (F : Fin m → Fin n) (φ : Φ) (σ : Sd) : PK × SK :=
  kg φ (eK (prfRow eD F σ))

/-- Encryption with noise from the oracle table `F`: `enc pk msg` at the coins
assembled by `eE` from the row of `F` at the coin `r`. -/
def encPrf (F : Fin m → Fin n) (pk : PK) (msg : M) (r : Sd) : C :=
  enc pk msg (eE (prfRow eD F r))

/-- A quantum IND-CPA adversary with coins in `ι` and oracle access to the noise
table: two messages from the public key and its coins, and from the public key,
the challenge ciphertext and its coins, an adversary with a pure initial state
querying the table. -/
structure QIndPrfAdv (ι : Type) (m n w q : ℕ) (PK C M : Type) where
  /-- The two messages. -/
  msgs : PK → ι → M × M
  /-- The adversary run on the public key and the challenge ciphertext. -/
  prog : PK → C → ι → QAdv m n w q
  /-- Every run starts from a pure state. -/
  pure : ∀ pk c i, ∃ ψ : Fin (m * n * w) → ℂ, (prog pk c i).init.val = vecMulVec ψ (star ψ)

/-- The message of `B` selected by the challenge bit `b`. -/
def QIndPrfAdv.msg (B : QIndPrfAdv ι m n w q PK C M) (pk : PK) (i : ι) (b : Bool) : M :=
  if b then (B.msgs pk i).2 else (B.msgs pk i).1

variable [Fintype Sd] [DecidableEq Sd] [Nonempty Sd] [Fintype Nc] [DecidableEq Nc] [NeZero n]
  [Fintype Φ] [Fintype ι]

/-- The probability that `B` outputs `1` in the IND-CPA experiment of the scheme
with noise from the oracle: public coins `φ`, adversary coins `i`, seeds
`(σ, r)` and table `F` uniform; the key pair `keygenPrf F φ σ`, the challenge
`encPrf F pk m_b r`, and `B` querying `F`. -/
def qIndPrfPr (B : QIndPrfAdv ι m n w q PK C M) (b : Bool) : ℝ≥0∞ :=
  avg fun ω : Φ × ι => avg fun sr : Sd × Sd => avg fun F : Fin m → Fin n =>
    prOut (B.prog (keygenPrf eD kg eK F ω.1 sr.1).1
      (encPrf eD enc eE F (keygenPrf eD kg eK F ω.1 sr.1).1
        (B.msg (keygenPrf eD kg eK F ω.1 sr.1).1 ω.2 b) sr.2) ω.2) F

/-- The probability that `B` outputs `1` in the IND-CPA experiment with the
noise rows `a`, `b'` uniform and independent of the table `F` that `B` queries. -/
def qIndIdealPr (B : QIndPrfAdv ι m n w q PK C M) (b : Bool) : ℝ≥0∞ :=
  avg fun ω : Φ × ι => avg fun p : (Nc → Fin n) × (Nc → Fin n) × (Fin m → Fin n) =>
    prOut (B.prog (kg ω.1 (eK p.1)).1
      (enc (kg ω.1 (eK p.1)).1 (B.msg (kg ω.1 (eK p.1)).1 ω.2 b) (eE p.2.1)) ω.2) p.2.2

/-- The probability that `B` outputs `1` in the IND-CPA experiment of the scheme
with uniform key-generation seed `ks` and uniform coins `ρ`, `B` querying a
uniform table `F`. -/
def qIndUnifPr [Fintype KS] [Fintype R] (B : QIndPrfAdv ι m n w q PK C M) (b : Bool) :
    ℝ≥0∞ :=
  avg fun ω : Φ × ι => avg fun ks : KS => avg fun ρ : R => avg fun F : Fin m → Fin n =>
    prOut (B.prog (kg ω.1 ks).1 (enc (kg ω.1 ks).1 (B.msg (kg ω.1 ks).1 ω.2 b) ρ) ω.2) F

/-- The IND-CPA experiments of the two schemes differ by at most
`|Sd|⁻¹ + 4 √(q · 8 q |Sd|⁻¹)`. -/
theorem absDiff_qIndPrfPr_qIndIdealPr [Nonempty Φ] [Nonempty ι]
    (B : QIndPrfAdv ι m n w q PK C M) (b : Bool) :
    absDiff (qIndPrfPr eD kg enc eK eE B b) (qIndIdealPr kg enc eK eE B b) ≤
      (Fintype.card Sd : ℝ≥0∞)⁻¹ +
        4 * ((q : ℝ≥0∞) * (8 * q * (Fintype.card Sd : ℝ≥0∞)⁻¹)) ^ (1 / 2 : ℝ) := by
  have hwt : ∑ _ω : Φ × ι, (Fintype.card (Φ × ι) : ℝ≥0∞)⁻¹ = 1 := by
    simpa using sum_inv_mul_const (α := Φ × ι) (1 : ℝ≥0∞)
  exact absDiff_prfReal_prfIdeal eD (fun _ : Φ × ι => (Fintype.card (Φ × ι) : ℝ≥0∞)⁻¹)
    (fun ω a b' => ((kg ω.1 (eK a)).1,
      enc (kg ω.1 (eK a)).1 (B.msg (kg ω.1 (eK a)).1 ω.2 b) (eE b')))
    (fun ω x => B.prog x.1 x.2 ω.2) (fun _ _ F => F) (fun _ _ t => some (eD.symm t).1) hwt
    (fun _ _ F F' t h => by
      have := congrFun (h _ rfl) (eD.symm t).2
      simpa [prfRow] using this)
    (fun ω x => B.pure x.1 x.2 ω.2)

/-- `e` sends the uniform distribution to the uniform distribution. -/
def PushesUniform {α β : Type} [Fintype α] [Fintype β] (e : α → β) : Prop :=
  ∀ g : β → ℝ≥0∞, avg (fun x => g (e x)) = avg g

/-- When `eK` and `eE` push the uniform distribution to the uniform
distribution, the IND-CPA experiment with uniform noise rows is the experiment of
the scheme with uniform key-generation seed and coins. -/
theorem qIndIdealPr_eq_uniform [Fintype KS] [Fintype R] (hK : PushesUniform eK)
    (hE : PushesUniform eE) (B : QIndPrfAdv ι m n w q PK C M) (b : Bool) :
    qIndIdealPr kg enc eK eE B b = qIndUnifPr kg enc B b := by
  unfold qIndIdealPr qIndUnifPr
  refine congrArg avg (funext fun ω => ?_)
  set h : KS → R → (Fin m → Fin n) → ℝ≥0∞ := fun ks ρ F =>
    prOut (B.prog (kg ω.1 ks).1 (enc (kg ω.1 ks).1 (B.msg (kg ω.1 ks).1 ω.2 b) ρ) ω.2) F
  calc (avg fun p : (Nc → Fin n) × (Nc → Fin n) × (Fin m → Fin n) =>
          h (eK p.1) (eE p.2.1) p.2.2)
      = avg fun a => avg fun b' => avg fun F => h (eK a) (eE b') F := by
        rw [avg_prod]
        exact congrArg avg (funext fun a => avg_prod _)
    _ = avg fun a => avg fun ρ => avg fun F => h (eK a) ρ F :=
        congrArg avg (funext fun a => hE (fun ρ => avg fun F => h (eK a) ρ F))
    _ = avg fun ks => avg fun ρ => avg fun F => h ks ρ F :=
        hK (fun ks => avg fun ρ => avg fun F => h ks ρ F)

/-- The IND-CPA advantage of `B` against the scheme with noise from the oracle
is at most its advantage against the scheme with uniform key-generation seed and
coins, plus twice `|Sd|⁻¹ + 4 √(q · 8 q |Sd|⁻¹)`. -/
theorem qIndPrfAdv_le [Nonempty Φ] [Nonempty ι] [Fintype KS] [Fintype R]
    (hK : PushesUniform eK) (hE : PushesUniform eE) (B : QIndPrfAdv ι m n w q PK C M) :
    absDiff (qIndPrfPr eD kg enc eK eE B true) (qIndPrfPr eD kg enc eK eE B false) ≤
      absDiff (qIndUnifPr kg enc B true) (qIndUnifPr kg enc B false) +
        2 * ((Fintype.card Sd : ℝ≥0∞)⁻¹ +
          4 * ((q : ℝ≥0∞) * (8 * q * (Fintype.card Sd : ℝ≥0∞)⁻¹)) ^ (1 / 2 : ℝ)) := by
  have h1 := absDiff_qIndPrfPr_qIndIdealPr eD kg enc eK eE B true
  have h0 := absDiff_qIndPrfPr_qIndIdealPr eD kg enc eK eE B false
  rw [qIndIdealPr_eq_uniform kg enc eK eE hK hE] at h1 h0
  calc _ ≤ absDiff (qIndPrfPr eD kg enc eK eE B true) (qIndUnifPr kg enc B true) +
        absDiff (qIndUnifPr kg enc B true) (qIndPrfPr eD kg enc eK eE B false) :=
        absDiff_triangle _ _ _
    _ ≤ absDiff (qIndPrfPr eD kg enc eK eE B true) (qIndUnifPr kg enc B true) +
        (absDiff (qIndUnifPr kg enc B true) (qIndUnifPr kg enc B false) +
          absDiff (qIndUnifPr kg enc B false) (qIndPrfPr eD kg enc eK eE B false)) :=
        add_le_add le_rfl (absDiff_triangle _ _ _)
    _ ≤ _ := by
        rw [absDiff_comm (qIndUnifPr kg enc B false)]
        calc _ ≤ ((Fintype.card Sd : ℝ≥0∞)⁻¹ +
                4 * ((q : ℝ≥0∞) * (8 * q * (Fintype.card Sd : ℝ≥0∞)⁻¹)) ^ (1 / 2 : ℝ)) +
              (absDiff (qIndUnifPr kg enc B true) (qIndUnifPr kg enc B false) +
                ((Fintype.card Sd : ℝ≥0∞)⁻¹ +
                  4 * ((q : ℝ≥0∞) * (8 * q * (Fintype.card Sd : ℝ≥0∞)⁻¹)) ^ (1 / 2 : ℝ))) :=
              add_le_add h1 (add_le_add le_rfl h0)
          _ = _ := by ring

end PKE

end CatCrypt.Crypto.MLKEM.PRFOracle
