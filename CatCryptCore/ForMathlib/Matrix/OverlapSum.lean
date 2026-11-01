/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Matrix.Order
public import CatCryptCore.ForMathlib.Matrix.TraceInequalities

/-!
# Sums of squares of self-adjoint operators bounded by pairwise overlaps

Let `G` be a finite additive group and `(R_g)_{g ∈ G}` self-adjoint operators on a complex
inner product space. If the overlaps are bounded along every translation,
`‖R_g R_{g+t}‖ ≤ c(t)` for all `g`, then `∑_g R_g² ≤ (∑_t c(t)) · 1`. The translations
`g ↦ g + t` are the mutually orthogonal permutations of Tomamichel–Fehr–Kaniewski–Wehner,
Lemma 2; the proof is by quadratic forms.

For `G = (Fin 2)ⁿ` and `c(t) = c^{|t|}` (`|t|` the Hamming weight) the bound is
`∑_t c^{|t|} = (1 + c)ⁿ` (`sum_pow_hammingWeight`), so averaged over `G` the sum is at most
`((1 + c)/2)ⁿ`: the winning probability of the `n`-fold monogamy-of-entanglement game.

Mathlib candidates for `Mathlib/Analysis/InnerProductSpace/` and
`Mathlib/Analysis/CStarAlgebra/Matrix.lean`.

## Main results

* `InnerProductSpace.sum_norm_sq_le_of_overlap`: `∑_g ‖R_g v‖² ≤ (∑_t c(t)) ‖v‖²`.
* `Matrix.posSemidef_smul_one_sub_sum_of_overlap`: `(∑_t c(t)) · 1 − ∑_g R_g² ≥ 0` for
  Hermitian matrices, with the `L²` operator norm.
* `Matrix.re_trace_mul_sum_le_of_overlap`: `Re tr(ρ ∑_g R_g²) ≤ ∑_t c(t)` for a density
  matrix `ρ`.
* `sum_pow_hammingWeight`: `∑_{t : Fin n → Fin 2} c^{|t|} = (1 + c)ⁿ`.
* `Matrix.average_re_trace_le_of_hammingOverlap`: the `n`-fold average bound
  `|G|⁻¹ ∑_θ Re tr(ρ R_θ²) ≤ ((1 + c)/2)ⁿ`.
* `ContinuousLinearMap.norm_sum_mul_le_of_orthogonal`: `‖∑_i K_i E_i‖ ≤ max_i ‖K_i‖` for
  pairwise orthogonal star projections `E_i` commuting with `K_i`.
* `MonogamyGame.sum_re_inner_winOp_le`: the monogamy-of-entanglement bound
  `∑_θ ⟨v, Π_θ v⟩ ≤ (∑_t c(t)) ‖v‖²` for a projective strategy of Alice, Bob and Eve whose
  Alice measurements overlap by `‖P_θ(x) P_{θ+t}(y)‖ ≤ c(t)`; `average_re_inner_winOp_le`
  is the `n`-fold form `((1 + c)/2)ⁿ`.
* `IsStarProjection.norm_mul_sq_le`, `Matrix.norm_toEuclideanCLM_vecMulVec_kronecker_one_mul_le`:
  `‖P_a P_b‖ ≤ |⟨a, b⟩|` for the rank-one projectors `|a⟩⟨a| ⊗ 1` of unit vectors.

## References

* Tomamichel, M., Fehr, S., Kaniewski, J., Wehner, S. — *A monogamy-of-entanglement game
  with applications to device-independent quantum cryptography*, New J. Phys. 15 (2013),
  Lemma 2 and Theorem 3.
-/

@[expose] public section

set_option autoImplicit false

open scoped InnerProductSpace Matrix ComplexOrder MatrixOrder

noncomputable section

namespace InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {G : Type*} [Fintype G] [AddGroup G]

/-- **Overlap bound for a sum of squares.** For symmetric operators `T_g` indexed by a finite
additive group with `‖⟪x, T_g T_{g+t} y⟫‖ ≤ c(t) ‖x‖ ‖y‖`, the quadratic form of `∑_g T_g²`
is at most `∑_t c(t)`: `∑_g ‖T_g v‖² ≤ (∑_t c(t)) ‖v‖²`. -/
theorem sum_norm_sq_le_of_overlap (T : G → H →ₗ[ℂ] H) (hT : ∀ g, (T g).IsSymmetric)
    (c : G → ℝ) (hc : ∀ t, 0 ≤ c t)
    (hov : ∀ g t x y, ‖⟪x, T g (T (g + t) y)⟫_ℂ‖ ≤ c t * ‖x‖ * ‖y‖) (v : H) :
    ∑ g, ‖T g v‖ ^ 2 ≤ (∑ t, c t) * ‖v‖ ^ 2 := by
  set w : G → H := fun g => T g v with hw
  set S : ℝ := ∑ g, ‖w g‖ ^ 2 with hSdef
  set y : H := ∑ g, T g (w g) with hy
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun g _ => sq_nonneg _
  have hSy : S = RCLike.re ⟪v, y⟫_ℂ := by
    rw [hy, inner_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← hT g, inner_self_eq_norm_sq]
  have hSle : S ≤ ‖v‖ * ‖y‖ := hSy ▸ (RCLike.re_le_norm _).trans (norm_inner_le_norm v y)
  have hyy : ‖y‖ ^ 2 ≤ (∑ t, c t) * S := by
    have h1 : ‖y‖ ^ 2 = ∑ g, ∑ t, RCLike.re ⟪w g, T g (T (g + t) (w (g + t)))⟫_ℂ := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hy, sum_inner, map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [inner_sum, map_sum, ← Equiv.sum_comp (Equiv.addLeft g)]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [Equiv.coe_addLeft]
      rw [hT g]
    have h2 : ∀ g t, RCLike.re ⟪w g, T g (T (g + t) (w (g + t)))⟫_ℂ
        ≤ c t * ((‖w g‖ ^ 2 + ‖w (g + t)‖ ^ 2) / 2) := by
      intro g t
      refine (RCLike.re_le_norm _).trans ((hov g t _ _).trans ?_)
      have := two_mul_le_add_sq ‖w g‖ ‖w (g + t)‖
      nlinarith [hc t]
    rw [h1]
    calc ∑ g, ∑ t, RCLike.re ⟪w g, T g (T (g + t) (w (g + t)))⟫_ℂ
        ≤ ∑ g, ∑ t, c t * ((‖w g‖ ^ 2 + ‖w (g + t)‖ ^ 2) / 2) :=
          Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun t _ => h2 g t
      _ = ∑ t, c t * S := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          have hshift : ∑ x, ‖w (x + t)‖ ^ 2 = S :=
            Equiv.sum_comp (Equiv.addRight t) (fun h => ‖w h‖ ^ 2)
          rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, hshift]
          ring
      _ = (∑ t, c t) * S := by rw [Finset.sum_mul]
  have hfin : S * S ≤ (∑ t, c t) * ‖v‖ ^ 2 * S := by
    have hy0 := norm_nonneg y
    have hv0 := norm_nonneg v
    nlinarith [mul_le_mul hSle hSle hS0 (by positivity)]
  rcases hS0.eq_or_lt with h | h
  · rw [← h]
    exact mul_nonneg (Finset.sum_nonneg fun t _ => hc t) (sq_nonneg _)
  · exact le_of_mul_le_mul_right hfin h

end InnerProductSpace

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*}

/-- Orthogonal star projections have orthogonal ranges: `⟪E_i a, E_j b⟫ = 0` for `i ≠ j`. -/
theorem inner_apply_eq_zero_of_orthogonal {E : ι → H →L[ℂ] H}
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0)
    {i j : ι} (hij : i ≠ j) (a b : H) : ⟪E i a, E j b⟫_ℂ = 0 := by
  have h := (hE i).isSelfAdjoint.isSymmetric a (E j b)
  simp only [coe_coe] at h
  rw [h, show E i (E j b) = (E i * E j) b from rfl, horth i j hij, zero_apply,
    inner_zero_right]

/-- **Pythagoras for orthogonal star projections.**
`‖∑_i E_i a_i‖² = ∑_i ‖E_i a_i‖²`. -/
theorem norm_sum_apply_sq_of_orthogonal [Fintype ι] {E : ι → H →L[ℂ] H}
    (hE : ∀ i, IsStarProjection (E i)) (horth : ∀ i j, i ≠ j → E i * E j = 0) (a : ι → H) :
    ‖∑ i, E i (a i)‖ ^ 2 = ∑ i, ‖E i (a i)‖ ^ 2 := by
  classical
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i
    (fun j _ hji => inner_apply_eq_zero_of_orthogonal hE horth (Ne.symm hji) _ _)
    (fun h => absurd (Finset.mem_univ i) h), inner_self_eq_norm_sq]

/-- **Norm of a block-diagonal operator.** For pairwise orthogonal star projections `E_i` and
operators `K_i` commuting with `E_i`, `‖∑_i K_i E_i‖ ≤ max_i ‖K_i‖`. -/
theorem norm_sum_mul_le_of_orthogonal [Fintype ι] (E K : ι → H →L[ℂ] H)
    (hE : ∀ i, IsStarProjection (E i))
    (horth : ∀ i j, i ≠ j → E i * E j = 0) (hcomm : ∀ i, K i * E i = E i * K i)
    {c : ℝ} (hc : 0 ≤ c) (hK : ∀ i, ‖K i‖ ≤ c) :
    ‖∑ i, K i * E i‖ ≤ c := by
  refine opNorm_le_bound _ hc fun v => ?_
  have hidem : ∀ i, E i * E i = E i := fun i => (hE i).isIdempotentElem.eq
  have hw : ∀ i, (K i * E i) v = E i (K i (E i v)) := by
    intro i
    calc (K i * E i) v = (K i * (E i * E i)) v := by rw [hidem i]
      _ = (E i * K i * E i) v := by rw [← mul_assoc, hcomm i]
      _ = E i (K i (E i v)) := rfl
  have hEv : ‖∑ i, E i v‖ ≤ ‖v‖ := by
    have hsq : ‖∑ i, E i v‖ ^ 2 = RCLike.re ⟪v, ∑ i, E i v⟫_ℂ := by
      rw [norm_sum_apply_sq_of_orthogonal hE horth (fun _ => v), inner_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h := (hE i).isSelfAdjoint.isSymmetric v (E i v)
      have hEE : E i (E i v) = E i v := by
        change (E i * E i) v = E i v
        rw [hidem i]
      simp only [coe_coe, hEE] at h
      grind only [inner_self_eq_norm_mul_norm]
    have hle := (RCLike.re_le_norm ⟪v, ∑ i, E i v⟫_ℂ).trans (norm_inner_le_norm v _)
    rw [← hsq] at hle
    nlinarith [norm_nonneg v, norm_nonneg (∑ i, E i v)]
  have hsq : ‖(∑ i, K i * E i) v‖ ^ 2 ≤ (c * ‖v‖) ^ 2 := by
    rw [sum_apply, Finset.sum_congr rfl fun i _ => hw i,
      norm_sum_apply_sq_of_orthogonal hE horth]
    calc ∑ i, ‖E i (K i (E i v))‖ ^ 2 ≤ ∑ i, c ^ 2 * ‖E i v‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← hw i, ← mul_pow]
          have := (le_opNorm (K i) (E i v)).trans
            (mul_le_mul_of_nonneg_right (hK i) (norm_nonneg _))
          gcongr
          exact this
      _ = c ^ 2 * ‖∑ i, E i v‖ ^ 2 := by
          rw [← Finset.mul_sum, norm_sum_apply_sq_of_orthogonal hE horth (fun _ => v)]
      _ ≤ (c * ‖v‖) ^ 2 := by
          rw [mul_pow]
          gcongr
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

end ContinuousLinearMap

/-- A sum of pairwise orthogonal star projections is a star projection. -/
theorem isStarProjection_sum_of_orthogonal {R : Type*} [Ring R] [StarRing R] {X : Type*}
    [Fintype X] (e : X → R) (he : ∀ x, IsStarProjection (e x))
    (horth : ∀ x x', x ≠ x' → e x * e x' = 0) : IsStarProjection (∑ x, e x) := by
  classical
  refine ⟨?_, isSelfAdjoint_sum _ fun x _ => (he x).isSelfAdjoint⟩
  change (∑ x, e x) * (∑ x, e x) = ∑ x, e x
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single x (fun x' _ hx' => horth x x' (Ne.symm hx'))
    (fun h => absurd (Finset.mem_univ x) h), (he x).isIdempotentElem.eq]

/-- Reordering a product of two triples of operators: if `b` and `c` commute past `p'` and `c`
commutes past `b'`, then `(p b c)(p' b' c') = (p p')(b b')(c c')`. -/
theorem mul_triple_mul_triple {R : Type*} [Ring R] (p b c p' b' c' : R) (h1 : c * p' = p' * c)
    (h2 : b * p' = p' * b) (h3 : c * b' = b' * c) :
    p * b * c * (p' * b' * c') = p * p' * (b * b') * (c * c') := by
  simp only [mul_assoc]
  rw [← mul_assoc c p', h1, mul_assoc p', ← mul_assoc b p', h2, mul_assoc p', ← mul_assoc c b',
    h3]
  simp only [mul_assoc]

namespace MonogamyGame

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {G : Type*} {X : Type*} [Fintype X]

/-- A family `M θ x` of measurements indexed by a basis label `θ`, each a family of pairwise
orthogonal star projections in the outcome `x`. -/
def IsProjFamily (M : G → X → H →L[ℂ] H) : Prop :=
  (∀ θ x, IsStarProjection (M θ x)) ∧ ∀ θ x x', x ≠ x' → M θ x * M θ x' = 0

/-- A **projective strategy** for the monogamy-of-entanglement game: Alice measures `P θ`,
Bob `B θ` and Eve `C θ`; each is a projective measurement in every basis `θ`, and the
operators of different parties commute. A tensor-product strategy on `A ⊗ B ⊗ C` is of this
form; a strategy with general measurements reduces to a projective one by Naimark dilation. -/
structure IsStrategy (P B C : G → X → H →L[ℂ] H) : Prop where
  /-- Alice's measurements are projective. -/
  proj_P : IsProjFamily P
  /-- Bob's measurements are projective. -/
  proj_B : IsProjFamily B
  /-- Eve's measurements are projective. -/
  proj_C : IsProjFamily C
  /-- Alice's and Bob's operators commute. -/
  comm_PB : ∀ θ θ' x x', P θ x * B θ' x' = B θ' x' * P θ x
  /-- Alice's and Eve's operators commute. -/
  comm_PC : ∀ θ θ' x x', P θ x * C θ' x' = C θ' x' * P θ x
  /-- Bob's and Eve's operators commute. -/
  comm_BC : ∀ θ θ' x x', B θ x * C θ' x' = C θ' x' * B θ x

/-- The **winning operator** of basis `θ`: Alice, Bob and Eve all obtain the same outcome,
`Π_θ = ∑ₓ P_θ(x) B_θ(x) C_θ(x)`. -/
def winOp (P B C : G → X → H →L[ℂ] H) (θ : G) : H →L[ℂ] H := ∑ x, P θ x * B θ x * C θ x

variable {P B C : G → X → H →L[ℂ] H}

/-- The winning operator of a projective strategy is a star projection. -/
theorem isStarProjection_winOp (hS : IsStrategy P B C) (θ : G) :
    IsStarProjection (winOp P B C θ) := by
  refine isStarProjection_sum_of_orthogonal _ (fun x => ?_) (fun x x' hx => ?_)
  · exact ((hS.proj_P.1 θ x).mul (hS.proj_B.1 θ x) (hS.comm_PB θ θ x x)).mul
      (hS.proj_C.1 θ x) (by
        change P θ x * B θ x * C θ x = C θ x * (P θ x * B θ x)
        rw [mul_assoc, hS.comm_BC, ← mul_assoc, hS.comm_PC, mul_assoc])
  · rw [mul_triple_mul_triple _ _ _ _ _ _ (hS.comm_PC θ θ x' x).symm
      (hS.comm_PB θ θ x' x).symm (hS.comm_BC θ θ x' x).symm, hS.proj_P.2 θ x x' hx, zero_mul,
      zero_mul]

/-- **Overlap of two winning operators.** For bases `θ ≠ θ'`,
`‖Π_θ Π_θ'‖ ≤ max_{x,y} ‖P_θ(x) P_θ'(y)‖`. -/
theorem norm_winOp_mul_winOp_le (hS : IsStrategy P B C) (θ θ' : G) {c : ℝ} (hc : 0 ≤ c)
    (hov : ∀ x y, ‖P θ x * P θ' y‖ ≤ c) :
    ‖winOp P B C θ * winOp P B C θ'‖ ≤ c := by
  classical
  have cPB : ∀ θ₁ θ₂ x₁ x₂, Commute (P θ₁ x₁) (B θ₂ x₂) := fun θ₁ θ₂ x₁ x₂ => hS.comm_PB _ _ _ _
  have cPC : ∀ θ₁ θ₂ x₁ x₂, Commute (P θ₁ x₁) (C θ₂ x₂) := fun θ₁ θ₂ x₁ x₂ => hS.comm_PC _ _ _ _
  have cBC : ∀ θ₁ θ₂ x₁ x₂, Commute (B θ₁ x₁) (C θ₂ x₂) := fun θ₁ θ₂ x₁ x₂ => hS.comm_BC _ _ _ _
  set Q : H →L[ℂ] H := ∑ x, P θ x * B θ x * 1 with hQ
  set Q' : H →L[ℂ] H := ∑ y, P θ' y * 1 * C θ' y with hQ'
  have hWQ : winOp P B C θ * Q = winOp P B C θ := by
    simp only [winOp, hQ, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single x (fun x' _ hx' => ?_) (fun h => absurd (Finset.mem_univ x) h)]
    · rw [mul_triple_mul_triple _ _ _ _ _ _ (cPC θ θ x x).eq.symm (cPB θ θ x x).eq.symm
        (cBC θ θ x x).eq.symm, (hS.proj_P.1 θ x).isIdempotentElem.eq,
        (hS.proj_B.1 θ x).isIdempotentElem.eq, mul_one]
    · rw [mul_triple_mul_triple _ _ _ _ _ _ (cPC θ θ x x').eq.symm (cPB θ θ x x').eq.symm
        (cBC θ θ x x').eq.symm, hS.proj_P.2 θ x' x hx', zero_mul, zero_mul]
  have hQW : Q' * winOp P B C θ' = winOp P B C θ' := by
    simp only [winOp, hQ', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single x (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ x) h)]
    · rw [mul_triple_mul_triple _ _ _ _ _ _ (cPC θ' θ' x x).eq.symm (by rw [one_mul, mul_one])
        (cBC θ' θ' x x).eq.symm, (hS.proj_P.1 θ' x).isIdempotentElem.eq,
        (hS.proj_C.1 θ' x).isIdempotentElem.eq, one_mul]
    · rw [mul_triple_mul_triple _ _ _ _ _ _ (cPC θ' θ' x i).eq.symm (by rw [one_mul, mul_one])
        (cBC θ' θ' x i).eq.symm, hS.proj_P.2 θ' i x hi, zero_mul, zero_mul]
  have hQQ : Q * Q' = ∑ q : X × X, (P θ q.1 * P θ' q.2) * (B θ q.1 * C θ' q.2) := by
    rw [hQ, hQ', Finset.sum_mul_sum,
      Fintype.sum_prod_type (f := fun q : X × X => P θ q.1 * P θ' q.2 * (B θ q.1 * C θ' q.2))]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [mul_triple_mul_triple _ _ _ _ _ _ (by rw [one_mul, mul_one]) (cPB θ' θ y x).eq.symm
      rfl, mul_one, one_mul, mul_assoc]
  have hblock : ‖Q * Q'‖ ≤ c := by
    rw [hQQ]
    apply ContinuousLinearMap.norm_sum_mul_le_of_orthogonal (ι := X × X)
      (fun q => B θ q.1 * C θ' q.2) (fun q => P θ q.1 * P θ' q.2)
    · intro q
      exact (hS.proj_B.1 θ q.1).mul (hS.proj_C.1 θ' q.2) (cBC θ θ' q.1 q.2)
    · intro q q' hq
      have h : B θ q.1 * C θ' q.2 * (B θ q'.1 * C θ' q'.2)
          = B θ q.1 * B θ q'.1 * (C θ' q.2 * C θ' q'.2) := by
        rw [mul_assoc, ← mul_assoc (C θ' q.2), ← (cBC θ θ' q'.1 q.2).eq]
        simp only [mul_assoc]
      rw [h]
      by_cases h1 : q.1 = q'.1
      · have h2 : q.2 ≠ q'.2 := fun h2 => hq (Prod.ext h1 h2)
        rw [hS.proj_C.2 θ' _ _ h2, mul_zero]
      · rw [hS.proj_B.2 θ _ _ h1, zero_mul]
    · intro q
      exact ((cPB θ θ q.1 q.1).mul_right (cPC θ θ' q.1 q.2)).mul_left
        ((cPB θ' θ q.2 q.1).mul_right (cPC θ' θ' q.2 q.2))
    · exact hc
    · intro q
      exact hov q.1 q.2
  calc ‖winOp P B C θ * winOp P B C θ'‖
      = ‖winOp P B C θ * (Q * Q') * winOp P B C θ'‖ := by
        rw [← mul_assoc, hWQ, mul_assoc, hQW]
    _ ≤ ‖winOp P B C θ‖ * ‖Q * Q'‖ * ‖winOp P B C θ'‖ :=
        (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ 1 * c * 1 := by
        gcongr
        · exact (isStarProjection_winOp hS θ).norm_le
        · exact (isStarProjection_winOp hS θ').norm_le
    _ = c := by ring

/-- **The monogamy-of-entanglement bound.** For a projective strategy whose Alice
measurements have overlaps `‖P_θ(x) P_{θ+t}(y)‖ ≤ c(t)` for `t ≠ 0`, with `1 ≤ c(0)`, every
state `v` satisfies `∑_θ ⟨v, Π_θ v⟩ ≤ (∑_t c(t)) ‖v‖²`. -/
theorem sum_re_inner_winOp_le [Fintype G] [AddGroup G] (hS : IsStrategy P B C) (c : G → ℝ)
    (hc : ∀ t, 0 ≤ c t) (hc0 : 1 ≤ c 0)
    (hov : ∀ θ t x y, t ≠ 0 → ‖P θ x * P (θ + t) y‖ ≤ c t) (v : H) :
    ∑ θ, RCLike.re ⟪v, winOp P B C θ v⟫_ℂ ≤ (∑ t, c t) * ‖v‖ ^ 2 := by
  have hproj := isStarProjection_winOp hS
  have hsym : ∀ θ, (winOp P B C θ : H →ₗ[ℂ] H).IsSymmetric :=
    fun θ => (hproj θ).isSelfAdjoint.isSymmetric
  have hnorm : ∀ θ t, ‖winOp P B C θ * winOp P B C (θ + t)‖ ≤ c t := by
    intro θ t
    by_cases ht : t = 0
    · subst ht
      rw [add_zero, (hproj θ).isIdempotentElem.eq]
      exact ((hproj θ).norm_le).trans hc0
    · exact norm_winOp_mul_winOp_le hS θ (θ + t) (hc t) fun x y => hov θ t x y ht
  have hkey := InnerProductSpace.sum_norm_sq_le_of_overlap
    (fun θ => (winOp P B C θ : H →ₗ[ℂ] H)) hsym c hc (fun θ t x y => by
      calc ‖⟪x, winOp P B C θ (winOp P B C (θ + t) y)⟫_ℂ‖
          ≤ ‖x‖ * ‖(winOp P B C θ * winOp P B C (θ + t)) y‖ := norm_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖winOp P B C θ * winOp P B C (θ + t)‖ * ‖y‖) := by
            gcongr
            exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖x‖ * (c t * ‖y‖) := by gcongr; exact hnorm θ t
        _ = c t * ‖x‖ * ‖y‖ := by ring) v
  refine le_of_eq_of_le (Finset.sum_congr rfl fun θ _ => ?_) hkey
  have h := hsym θ v (winOp P B C θ v)
  have hEE : winOp P B C θ (winOp P B C θ v) = winOp P B C θ v := by
    change (winOp P B C θ * winOp P B C θ) v = winOp P B C θ v
    rw [(hproj θ).isIdempotentElem.eq]
  simp only [ContinuousLinearMap.coe_coe, hEE] at h ⊢
  rw [← h, inner_self_eq_norm_sq]

end MonogamyGame

namespace Matrix

open scoped Matrix.Norms.L2Operator

variable {E : Type*} [Fintype E] [DecidableEq E] {G : Type*} [Fintype G] [AddGroup G]

/-- **Overlap bound in the Loewner order.** For Hermitian matrices `R_g` indexed by a finite
additive group with `‖R_g R_{g+t}‖ ≤ c(t)` in the `L²` operator norm,
`(∑_t c(t)) · 1 − ∑_g R_g²` is positive semidefinite. -/
theorem posSemidef_smul_one_sub_sum_of_overlap (R : G → Matrix E E ℂ)
    (hR : ∀ g, (R g).IsHermitian) (c : G → ℝ) (hc : ∀ t, 0 ≤ c t)
    (hov : ∀ g t, ‖R g * R (g + t)‖ ≤ c t) :
    (((∑ t, c t : ℝ) : ℂ) • (1 : Matrix E E ℂ) - ∑ g, R g * R g).PosSemidef := by
  set C : ℝ := ∑ t, c t with hC
  have hRsa : ∀ g, IsSelfAdjoint (toEuclideanCLM (𝕜 := ℂ) (R g)) :=
    fun g => (hR g).isSelfAdjoint.map _
  set T : G → EuclideanSpace ℂ E →ₗ[ℂ] EuclideanSpace ℂ E :=
    fun g => (toEuclideanCLM (𝕜 := ℂ) (R g) : EuclideanSpace ℂ E →ₗ[ℂ] EuclideanSpace ℂ E)
    with hTdef
  have hTsym : ∀ g, (T g).IsSymmetric := fun g => (hRsa g).isSymmetric
  have hTov : ∀ g t x y, ‖⟪x, T g (T (g + t) y)⟫_ℂ‖ ≤ c t * ‖x‖ * ‖y‖ := by
    intro g t x y
    have hTT : T g (T (g + t) y) = toEuclideanCLM (𝕜 := ℂ) (R g * R (g + t)) y := by
      simp [hTdef, map_mul]
    rw [hTT]
    calc _ ≤ ‖x‖ * ‖toEuclideanCLM (𝕜 := ℂ) (R g * R (g + t)) y‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖toEuclideanCLM (𝕜 := ℂ) (R g * R (g + t))‖ * ‖y‖) := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖x‖ * (c t * ‖y‖) := by
          gcongr
          rw [l2_opNorm_toEuclideanCLM]
          exact hov g t
      _ = c t * ‖x‖ * ‖y‖ := by ring
  have hmap : toEuclideanCLM (𝕜 := ℂ) ((C : ℂ) • (1 : Matrix E E ℂ) - ∑ g, R g * R g)
      = (C : ℂ) • (1 : EuclideanSpace ℂ E →L[ℂ] EuclideanSpace ℂ E)
        - ∑ g, toEuclideanCLM (𝕜 := ℂ) (R g) * toEuclideanCLM (𝕜 := ℂ) (R g) := by
    simp only [map_sub, map_smul, map_one, map_sum, map_mul]
  have hsa : IsSelfAdjoint ((C : ℂ) • (1 : Matrix E E ℂ) - ∑ g, R g * R g) :=
    IsSelfAdjoint.sub (IsSelfAdjoint.smul (Complex.conj_ofReal C) (IsSelfAdjoint.one _))
      (isSelfAdjoint_sum _ fun g _ => by simpa [pow_two] using (hR g).isSelfAdjoint.pow 2)
  rw [← isPositive_toEuclideanLin_iff, ← coe_toEuclideanCLM_eq_toEuclideanLin]
  refine ⟨(hsa.map (toEuclideanCLM (𝕜 := ℂ))).isSymmetric, fun x => ?_⟩
  have hsq : ∀ g, RCLike.re ⟪T g (T g x), x⟫_ℂ = ‖T g x‖ ^ 2 := by
    intro g
    rw [hTsym g, inner_self_eq_norm_sq]
  have hkey := InnerProductSpace.sum_norm_sq_le_of_overlap T hTsym c hc hTov x
  rw [hmap]
  simp only [hTdef, ContinuousLinearMap.coe_coe] at hsq hkey
  have hexp : ((C : ℂ) • (1 : EuclideanSpace ℂ E →L[ℂ] EuclideanSpace ℂ E)
      - ∑ g, toEuclideanCLM (𝕜 := ℂ) (R g) * toEuclideanCLM (𝕜 := ℂ) (R g)) x
      = (C : ℂ) • x - ∑ g, toEuclideanCLM (𝕜 := ℂ) (R g) (toEuclideanCLM (𝕜 := ℂ) (R g) x) := by
    simp
  rw [ContinuousLinearMap.coe_coe, hexp, inner_sub_left, inner_smul_left, sum_inner, map_sub,
    map_sum]
  simp only [hsq, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K]
  refine sub_nonneg.mpr (hkey.trans_eq ?_)
  simp [hC, ← Complex.ofReal_pow]

/-- **Overlap bound against a state.** Under the hypotheses of
`posSemidef_smul_one_sub_sum_of_overlap`, a density matrix `ρ` (positive semidefinite, of
trace one) satisfies `Re tr(ρ ∑_g R_g²) ≤ ∑_t c(t)`. -/
theorem re_trace_mul_sum_le_of_overlap (R : G → Matrix E E ℂ)
    (hR : ∀ g, (R g).IsHermitian) (c : G → ℝ) (hc : ∀ t, 0 ≤ c t)
    (hov : ∀ g t, ‖R g * R (g + t)‖ ≤ c t) {ρ : Matrix E E ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) :
    (ρ * ∑ g, R g * R g).trace.re ≤ ∑ t, c t := by
  have h := hρ.re_trace_mul_nonneg (posSemidef_smul_one_sub_sum_of_overlap R hR c hc hov)
  rw [Matrix.mul_sub, trace_sub, Complex.sub_re, Matrix.mul_smul, Matrix.mul_one,
    trace_smul, htr] at h
  simpa using h

end Matrix

/-- The **Hamming weight** of `t : Fin n → Fin 2`: the number of coordinates `i` with
`t i ≠ 0`. -/
def hammingWeight {n : ℕ} (t : Fin n → Fin 2) : ℕ :=
  (Finset.univ.filter fun i => t i ≠ 0).card

/-- **Sum of powers of the Hamming weight.** `∑_{t : Fin n → Fin 2} c^{|t|} = (1 + c)ⁿ`. -/
theorem sum_pow_hammingWeight (n : ℕ) (c : ℝ) :
    ∑ t : Fin n → Fin 2, c ^ hammingWeight t = (1 + c) ^ n := by
  have hpt : ∀ t : Fin n → Fin 2,
      c ^ hammingWeight t = ∏ i, (if t i = 0 then (1 : ℝ) else c) := by
    intro t
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, hammingWeight]
  have h2 : ∑ a : Fin 2, (if a = 0 then (1 : ℝ) else c) = 1 + c :=
    Fin.sum_univ_two _
  simp only [hpt]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (a : Fin 2) => if a = 0 then (1 : ℝ) else c)]
  simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

namespace Matrix

open scoped Matrix.Norms.L2Operator

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **`n`-fold average bound.** For Hermitian matrices `R_θ` indexed by `θ : Fin n → Fin 2`
with overlaps `‖R_θ R_{θ+t}‖ ≤ c^{|t|}`, `c ≥ 0`, and a density matrix `ρ`, the average
`2⁻ⁿ ∑_θ Re tr(ρ R_θ²)` is at most `((1 + c)/2)ⁿ`. -/
theorem average_re_trace_le_of_hammingOverlap {n : ℕ} (R : (Fin n → Fin 2) → Matrix E E ℂ)
    (hR : ∀ θ, (R θ).IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (hov : ∀ θ t, ‖R θ * R (θ + t)‖ ≤ c ^ hammingWeight t) {ρ : Matrix E E ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    (1 / 2 ^ n : ℝ) * ∑ θ, (ρ * (R θ * R θ)).trace.re ≤ ((1 + c) / 2) ^ n := by
  have h := re_trace_mul_sum_le_of_overlap R hR (fun t => c ^ hammingWeight t)
    (fun t => pow_nonneg hc _) hov hρ htr
  rw [sum_pow_hammingWeight, Matrix.mul_sum, trace_sum, Complex.re_sum] at h
  rw [div_pow, one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right h (by positivity)

end Matrix

namespace MonogamyGame

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {X : Type*} [Fintype X] {n : ℕ} {P B C : (Fin n → Fin 2) → X → H →L[ℂ] H}

/-- **`n`-fold monogamy bound.** For a projective strategy with bases `θ : Fin n → Fin 2`
whose Alice measurements have overlaps `‖P_θ(x) P_{θ+t}(y)‖ ≤ c^{|t|}` for `t ≠ 0`, the
winning probability on a unit vector, averaged over the `2ⁿ` bases, is at most
`((1 + c)/2)ⁿ`. -/
theorem average_re_inner_winOp_le (hS : IsStrategy P B C) {c : ℝ} (hc : 0 ≤ c)
    (hov : ∀ θ t x y, t ≠ 0 → ‖P θ x * P (θ + t) y‖ ≤ c ^ hammingWeight t) {v : H}
    (hv : ‖v‖ = 1) :
    (1 / 2 ^ n : ℝ) * ∑ θ, RCLike.re ⟪v, winOp P B C θ v⟫_ℂ ≤ ((1 + c) / 2) ^ n := by
  have h0 : hammingWeight (0 : Fin n → Fin 2) = 0 := by simp [hammingWeight]
  have h := sum_re_inner_winOp_le hS (fun t => c ^ hammingWeight t) (fun t => pow_nonneg hc _)
    (by rw [h0, pow_zero]) hov v
  rw [sum_pow_hammingWeight, hv, one_pow, mul_one] at h
  rw [div_pow, one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right h (by positivity)

end MonogamyGame

/-- **Overlap of two star projections.** In a C*-ring, star projections `p`, `q` with
`q p q = s • q` for a real `s ≥ 0` satisfy `‖p q‖² ≤ s`. -/
theorem IsStarProjection.norm_mul_sq_le {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
    [NormedSpace ℂ A] {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q) {s : ℝ}
    (hs : 0 ≤ s) (hqpq : q * p * q = (s : ℂ) • q) : ‖p * q‖ ^ 2 ≤ s := by
  have h1 : star (p * q) * (p * q) = q * p * q := by
    rw [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, mul_assoc,
      ← mul_assoc p p, hp.isIdempotentElem.eq, mul_assoc]
  rw [sq, ← CStarRing.norm_star_mul_self, h1, hqpq, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg hs]
  exact mul_le_of_le_one_right hs hq.norm_le

namespace Matrix

open scoped Kronecker

variable {A : Type*} [Fintype A] {R : Type*} [Fintype R] [DecidableEq R]

/-- The rank-one projector `|a⟩⟨a|` of a unit vector, lifted to `A × R` as `|a⟩⟨a| ⊗ 1`, is
a star projection. -/
theorem isStarProjection_vecMulVec_kronecker_one {a : A → ℂ} (ha : star a ⬝ᵥ a = 1) :
    IsStarProjection (vecMulVec a (star a) ⊗ₖ (1 : Matrix R R ℂ)) := by
  refine ⟨?_, ?_⟩
  · change _ * _ = _
    rw [← mul_kronecker_mul, vecMulVec_mul_vecMulVec, ha, one_smul, Matrix.one_mul]
  · change star _ = _
    rw [star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_vecMulVec, star_star,
      conjTranspose_one]

/-- The lifted rank-one operators `P_v = |v⟩⟨v| ⊗ 1` satisfy
`P_b P_a P_b = |⟨a, b⟩|² P_b`. -/
theorem vecMulVec_kronecker_one_mul_mul (a b : A → ℂ) :
    (vecMulVec b (star b) ⊗ₖ (1 : Matrix R R ℂ)) * (vecMulVec a (star a) ⊗ₖ 1)
      * (vecMulVec b (star b) ⊗ₖ 1)
      = ((Complex.normSq (star a ⬝ᵥ b) : ℝ) : ℂ) • (vecMulVec b (star b) ⊗ₖ 1) := by
  rw [← mul_kronecker_mul, Matrix.one_mul, ← mul_kronecker_mul, Matrix.one_mul,
    ← smul_kronecker, vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec]
  congr 1
  rw [smul_dotProduct, vecMulVec_smul, Complex.normSq_eq_conj_mul_self, smul_eq_mul]
  congr 2
  simp [dotProduct, mul_comm]

/-- **Overlap of two lifted rank-one projectors.** For unit vectors `a`, `b`, the operators
`|a⟩⟨a| ⊗ 1` and `|b⟩⟨b| ⊗ 1` on `ℓ²(A × R)` have `‖P_a P_b‖ ≤ |⟨a, b⟩|`. -/
theorem norm_toEuclideanCLM_vecMulVec_kronecker_one_mul_le [DecidableEq A] {a b : A → ℂ}
    (ha : star a ⬝ᵥ a = 1) (hb : star b ⬝ᵥ b = 1) :
    ‖toEuclideanCLM (𝕜 := ℂ) (vecMulVec a (star a) ⊗ₖ (1 : Matrix R R ℂ))
      * toEuclideanCLM (𝕜 := ℂ) (vecMulVec b (star b) ⊗ₖ (1 : Matrix R R ℂ))‖
      ≤ ‖star a ⬝ᵥ b‖ := by
  have hp := (isStarProjection_vecMulVec_kronecker_one (R := R) ha).map
    (toEuclideanCLM (𝕜 := ℂ) (n := A × R))
  have hq := (isStarProjection_vecMulVec_kronecker_one (R := R) hb).map
    (toEuclideanCLM (𝕜 := ℂ) (n := A × R))
  have h := IsStarProjection.norm_mul_sq_le hp hq (Complex.normSq_nonneg _) (by
    rw [← map_mul, ← map_mul, vecMulVec_kronecker_one_mul_mul, map_smul])
  rw [Complex.normSq_eq_norm_sq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

end Matrix
