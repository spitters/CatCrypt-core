/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.SolovayKitaev.SU2

/-!
# The balanced group commutator in `SU(2)`

The group commutator `gc V W = V W V† W†`. An element `U ∈ SU(2)` with `‖U - 1‖ ≤ δ ≤ 1` is a
group commutator `gc V W` of two elements with `‖V - 1‖, ‖W - 1‖ ≤ 2 √δ` (the balanced
commutator of Dawson–Nielsen, §3): the commutator of the rotations by `φ` about the `x` and `y`
axes has trace `2 - 4 sin⁴ (φ / 2)`, so for a suitable `φ` it is conjugate to `U`, and
conjugating both rotations gives `V` and `W`. The commutator is stable under perturbation:
`‖gc V W - gc V' W'‖ ≤ 8 d Δ + 4 Δ²` for unitaries with `‖V - 1‖, ‖W - 1‖ ≤ d ≤ 1` and
`‖V - V'‖, ‖W - W'‖ ≤ Δ`. Matrices carry the `ℓ²` operator norm.

## Main results

* `SolovayKitaev.trace_gc_rot_rot` — the trace of the commutator of two orthogonal rotations.
* `SolovayKitaev.exists_gc_eq` — the balanced group commutator, with `cGC = 2` and `δGC = 1`.
* `SolovayKitaev.norm_gc_sub_gc_le` — the perturbation bound of the commutator.
* `SolovayKitaev.gcChoice` — a choice of the two factors, with `gc_gcChoice` and the bounds
  `norm_gcChoice_fst_sub_one_le`, `norm_gcChoice_snd_sub_one_le`.

## References

* C. M. Dawson, M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006).
* M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information*, Appendix 3.
-/

@[expose] public section

set_option autoImplicit false

open Complex Matrix
open scoped Matrix.Norms.L2Operator

namespace SolovayKitaev

/-- The group commutator `V W V† W†`. -/
def gc (V W : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  V * W * star V * star W

/-- The constant of the balanced group commutator: the factors of `U` lie within
`cGC * √‖U - 1‖` of the identity. -/
def cGC : ℝ := 2

/-- The radius `‖U - 1‖ ≤ δGC` within which the balanced group commutator is stated. -/
def δGC : ℝ := 1

/-- The commutator of the rotations by `φ` about the `x` and `y` axes has trace
`2 - 4 sin⁴ (φ / 2)`. -/
theorem trace_gc_rot_rot (φ : ℝ) :
    trace (gc (rot (EuclideanSpace.single 0 1) φ) (rot (EuclideanSpace.single 1 1) φ)) =
      2 - 4 * (Real.sin (φ / 2) : ℂ) ^ 4 := by
  have hC : ((Real.cos (φ * (1 / 2)) : ℂ)) ^ 2 + (Real.sin (φ * (1 / 2)) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq _
  have h4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]; simp
  have h6 : I ^ 6 = -1 := by rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul]; norm_num
  simp [gc, rot, pauliVec, pauli, σx, σy, σz, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.star_eq_conjTranspose, -Complex.ofReal_cos, -Complex.ofReal_sin, Complex.conj_ofReal]
  ring_nf
  simp only [h4, h6, Complex.I_sq]
  linear_combination
    (2 * ((Real.cos (φ * (1 / 2)) : ℂ) ^ 2 + (Real.sin (φ * (1 / 2)) : ℂ) ^ 2 + 1)) * hC

/-- **Balanced group commutator** (Dawson–Nielsen, §3). An element `U ∈ SU(2)` with
`‖U - 1‖ ≤ δ ≤ δGC` is the commutator of two elements within `cGC * √δ` of the identity. -/
theorem exists_gc_eq {U : SU2} {δ : ℝ} (hU : ‖(U : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ δ)
    (hδ : δ ≤ δGC) :
    ∃ V W : SU2, (U : Matrix (Fin 2) (Fin 2) ℂ) = gc V W ∧
      ‖(V : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ cGC * Real.sqrt δ ∧
      ‖(W : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ cGC * Real.sqrt δ := by
  obtain ⟨n, θ, hn, h0, h2π, hU'⟩ := exists_rot_eq U
  have hnorm : ‖(U : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ = 2 * Real.sin (θ / 4) := by
    rw [hU', norm_rot_sub_one hn, abs_of_nonneg]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hs0 : 0 ≤ Real.sin (θ / 4) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hs1 : Real.sin (θ / 4) ≤ δ / 2 := by
    have := hU; unfold δGC at hδ; linarith
  have hδ1 : δ ≤ 1 := hδ
  set s := Real.sin (θ / 4) with hs
  set a := Real.arcsin (Real.sqrt s) with ha
  have hsq1 : Real.sqrt s ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith
  have hsin : Real.sin a = Real.sqrt s :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg s]) hsq1
  have hcos0 : 0 ≤ Real.cos a := Real.cos_arcsin_nonneg _
  have hcos1 : Real.cos a ≤ 1 := Real.cos_le_one _
  have hx : ‖(EuclideanSpace.single (0 : Fin 3) (1 : ℝ))‖ = 1 := by simp
  have hy : ‖(EuclideanSpace.single (1 : Fin 3) (1 : ℝ))‖ = 1 := by simp
  let V0 : SU2 := ⟨rot (EuclideanSpace.single 0 1) (2 * a),
    rot_mem_specialUnitaryGroup hx _⟩
  let W0 : SU2 := ⟨rot (EuclideanSpace.single 1 1) (2 * a),
    rot_mem_specialUnitaryGroup hy _⟩
  let G : SU2 := V0 * W0 * star V0 * star W0
  have hG : (G : Matrix (Fin 2) (Fin 2) ℂ) = gc V0 W0 := rfl
  have htr : trace (U : Matrix (Fin 2) (Fin 2) ℂ) = trace (G : Matrix (Fin 2) (Fin 2) ℂ) := by
    have hc : Real.cos (θ / 2) = 1 - 2 * s ^ 2 := by
      rw [show θ / 2 = 2 * (θ / 4) by ring, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (θ / 4)]
    have h4 : (Real.sqrt s) ^ 4 = s ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hs0]
    rw [hG, hU', trace_rot]
    change _ = trace (gc (rot (EuclideanSpace.single 0 1) (2 * a))
      (rot (EuclideanSpace.single 1 1) (2 * a)))
    rw [trace_gc_rot_rot, show 2 * a / 2 = a by ring, hsin, hc]
    have h4' : ((Real.sqrt s : ℝ) : ℂ) ^ 4 = ((s ^ 2 : ℝ) : ℂ) := by
      rw [← h4]; push_cast; rfl
    rw [h4']
    push_cast
    ring
  obtain ⟨S, hS⟩ := exists_conj_of_trace_eq htr.symm
  have hSS' : star (S : Matrix (Fin 2) (Fin 2) ℂ) * (S : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem S.2.1
  have hcancel : ∀ Z : Matrix (Fin 2) (Fin 2) ℂ,
      star (S : Matrix (Fin 2) (Fin 2) ℂ) * ((S : Matrix (Fin 2) (Fin 2) ℂ) * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hSS', Matrix.one_mul]
  have hsin2 : Real.sin (2 * a / 4) ^ 2 ≤ δ := by
    have h1 : Real.sin (2 * a / 4) ^ 2 = 1 / 2 - Real.cos a / 2 := by
      have hc2 := Real.cos_two_mul (a / 2)
      rw [show 2 * (a / 2) = a by ring] at hc2
      rw [show 2 * a / 4 = a / 2 by ring]
      nlinarith [Real.sin_sq_add_cos_sq (a / 2)]
    have h2 : Real.sin a ^ 2 = s := by rw [hsin, Real.sq_sqrt hs0]
    nlinarith [Real.sin_sq_add_cos_sq a]
  have hbound : 2 * |Real.sin (2 * a / 4)| ≤ cGC * Real.sqrt δ := by
    unfold cGC
    have := Real.abs_le_sqrt hsin2
    linarith
  have hax : ∀ (X : SU2) (m : EuclideanSpace ℝ (Fin 3)), ‖m‖ = 1 →
      (X : Matrix (Fin 2) (Fin 2) ℂ) = rot m (2 * a) →
      ‖((S * X * star S : SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ cGC * Real.sqrt δ :=
    fun X m hm hX => by
    have e := conj_rot S m (2 * a)
    have := norm_rot_sub_one (n := adSO3 S m) (by rw [norm_adSO3, hm]) (2 * a)
    refine le_trans (le_of_eq ?_) hbound
    rw [← this, ← e, ← hX]
    rfl
  refine ⟨S * V0 * star S, S * W0 * star S, ?_, hax V0 _ hx rfl, hax W0 _ hy rfl⟩
  have hUS := congrArg Subtype.val hS
  rw [hUS]
  change (S : Matrix (Fin 2) (Fin 2) ℂ) * (G : Matrix (Fin 2) (Fin 2) ℂ) *
      star (S : Matrix (Fin 2) (Fin 2) ℂ) =
    gc ((S : Matrix (Fin 2) (Fin 2) ℂ) * V0 * star (S : Matrix (Fin 2) (Fin 2) ℂ))
      ((S : Matrix (Fin 2) (Fin 2) ℂ) * W0 * star (S : Matrix (Fin 2) (Fin 2) ℂ))
  rw [hG]
  simp only [gc, star_mul, star_star, Matrix.mul_assoc, hcancel]

private lemma gc_sub_one {V W : Matrix (Fin 2) (Fin 2) ℂ}
    (hV : V ∈ unitaryGroup (Fin 2) ℂ) (hW : W ∈ unitaryGroup (Fin 2) ℂ) :
    gc V W - 1 = (V * W - W * V) * (star V * star W) := by
  have h1 : V * star V = 1 := Unitary.mul_star_self_of_mem hV
  have h2 : W * star W = 1 := Unitary.mul_star_self_of_mem hW
  have : (V * W - W * V) * (star V * star W) = gc V W - W * (V * star V) * star W := by
    unfold gc; noncomm_ring
  rw [this, h1, Matrix.mul_one, h2]

/-- **Perturbation of the group commutator.** For unitaries `V, W` within `d ≤ 1` of the
identity and unitaries `V', W'` within `Δ` of them,
`‖gc V W - gc V' W'‖ ≤ 8 d Δ + 4 Δ²`. -/
theorem norm_gc_sub_gc_le {V W V' W' : Matrix (Fin 2) (Fin 2) ℂ} {d Δ : ℝ}
    (hV : V ∈ unitaryGroup (Fin 2) ℂ) (hW : W ∈ unitaryGroup (Fin 2) ℂ)
    (hV' : V' ∈ unitaryGroup (Fin 2) ℂ) (hW' : W' ∈ unitaryGroup (Fin 2) ℂ)
    (hVd : ‖V - 1‖ ≤ d) (hWd : ‖W - 1‖ ≤ d) (hd : d ≤ 1)
    (hVV' : ‖V - V'‖ ≤ Δ) (hWW' : ‖W - W'‖ ≤ Δ) :
    ‖gc V W - gc V' W'‖ ≤ 8 * d * Δ + 4 * Δ ^ 2 := by
  have nV : ‖V‖ = 1 := CStarRing.norm_of_mem_unitary hV
  have nW : ‖W‖ = 1 := CStarRing.norm_of_mem_unitary hW
  have nV' : ‖V'‖ = 1 := CStarRing.norm_of_mem_unitary hV'
  have nW' : ‖W'‖ = 1 := CStarRing.norm_of_mem_unitary hW'
  have sV' : ‖star V'‖ = 1 := by rw [norm_star, nV']
  have sW : ‖star W‖ = 1 := by rw [norm_star, nW]
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hVd
  have hΔ0 : 0 ≤ Δ := (norm_nonneg _).trans hVV'
  have e1 := gc_sub_one hV hW
  have e2 := gc_sub_one hV' hW'
  have hPP : ‖star V * star W - star V' * star W'‖ ≤ 2 * Δ := by
    have : star V * star W - star V' * star W' =
        star (V - V') * star W + star V' * star (W - W') := by
      simp only [star_sub]; noncomm_ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖star (V - V') * star W‖ ≤ Δ :=
      (norm_mul_le _ _).trans (by rw [sW, mul_one, norm_star]; exact hVV')
    have h2 : ‖star V' * star (W - W')‖ ≤ Δ :=
      (norm_mul_le _ _).trans (by rw [sV', one_mul, norm_star]; exact hWW')
    linarith
  have ha' : ‖V' - 1‖ ≤ d + Δ := by
    have : V' - 1 = (V - 1) - (V - V') := by abel
    rw [this]
    exact (norm_sub_le _ _).trans (by linarith)
  have hc : ‖(V * W - W * V)‖ ≤ 2 * d ^ 2 := by
    have : V * W - W * V = (V - 1) * (W - 1) - (W - 1) * (V - 1) := by noncomm_ring
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖(V - 1) * (W - 1)‖ ≤ d * d := (norm_mul_le _ _).trans (by gcongr)
    have h2 : ‖(W - 1) * (V - 1)‖ ≤ d * d := (norm_mul_le _ _).trans (by gcongr)
    nlinarith
  have hcc : ‖(V * W - W * V) - (V' * W' - W' * V')‖ ≤ 4 * d * Δ + 2 * Δ ^ 2 := by
    have : (V * W - W * V) - (V' * W' - W' * V') =
        ((V - V') * (W - 1) - (W - 1) * (V - V')) +
        ((V' - 1) * (W - W') - (W - W') * (V' - 1)) := by noncomm_ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(V - V') * (W - 1) - (W - 1) * (V - V')‖ ≤ 2 * (Δ * d) :=
      (norm_sub_le _ _).trans (by
        have a1 := norm_mul_le (V - V') (W - 1)
        have a2 := norm_mul_le (W - 1) (V - V')
        have b1 : ‖V - V'‖ * ‖W - 1‖ ≤ Δ * d := by gcongr
        have b2 : ‖W - 1‖ * ‖V - V'‖ ≤ d * Δ := by gcongr
        linarith)
    have h2 : ‖(V' - 1) * (W - W') - (W - W') * (V' - 1)‖ ≤ 2 * ((d + Δ) * Δ) :=
      (norm_sub_le _ _).trans (by
        have a1 := norm_mul_le (V' - 1) (W - W')
        have a2 := norm_mul_le (W - W') (V' - 1)
        have b1 : ‖V' - 1‖ * ‖W - W'‖ ≤ (d + Δ) * Δ := by gcongr
        have b2 : ‖W - W'‖ * ‖V' - 1‖ ≤ Δ * (d + Δ) := by gcongr
        linarith)
    nlinarith
  have hsplit : gc V W - gc V' W' = (V * W - W * V) * (star V * star W - star V' * star W') +
      ((V * W - W * V) - (V' * W' - W' * V')) * (star V' * star W') := by
    have : gc V W - gc V' W' = (gc V W - 1) - (gc V' W' - 1) := by abel
    rw [this, e1, e2]; noncomm_ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hP' : ‖star V' * star W'‖ ≤ 1 := (norm_mul_le _ _).trans (by
    rw [sV', norm_star, nW']; norm_num)
  have t1 : ‖(V * W - W * V) * (star V * star W - star V' * star W')‖ ≤ 2 * d ^ 2 * (2 * Δ) :=
    (norm_mul_le _ _).trans (by gcongr)
  have t2 : ‖((V * W - W * V) - (V' * W' - W' * V')) * (star V' * star W')‖ ≤
      4 * d * Δ + 2 * Δ ^ 2 :=
    (norm_mul_le _ _).trans (by
      calc _ ≤ (4 * d * Δ + 2 * Δ ^ 2) * 1 := by gcongr
        _ = _ := by ring)
  nlinarith [mul_nonneg hd0 hΔ0, mul_nonneg (mul_nonneg hd0 hΔ0) (sub_nonneg.2 hd)]

open Classical in
/-- A choice of the factors of the balanced group commutator of `U`, and `(1, 1)` when
`‖U - 1‖ > δGC`. -/
noncomputable def gcChoice (U : SU2) : SU2 × SU2 :=
  if h : ‖(U : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ δGC then
    ((exists_gc_eq le_rfl h).choose, (exists_gc_eq le_rfl h).choose_spec.choose)
  else (1, 1)

/-- The chosen factors have commutator `U` when `‖U - 1‖ ≤ δGC`. -/
theorem gc_gcChoice {U : SU2} (hU : ‖(U : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ δGC) :
    (U : Matrix (Fin 2) (Fin 2) ℂ) = gc (gcChoice U).1 (gcChoice U).2 := by
  simp only [gcChoice, hU, ↓reduceDIte]
  exact (exists_gc_eq le_rfl hU).choose_spec.choose_spec.1

/-- The first chosen factor lies within `cGC * √δ` of the identity. -/
theorem norm_gcChoice_fst_sub_one_le {U : SU2} {δ : ℝ}
    (hU : ‖(U : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ δ) (hδ : δ ≤ δGC) :
    ‖((gcChoice U).1 : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ cGC * Real.sqrt δ := by
  have h : ‖(U : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ δGC := hU.trans hδ
  simp only [gcChoice, h, ↓reduceDIte]
  refine ((exists_gc_eq le_rfl h).choose_spec.choose_spec.2.1).trans ?_
  unfold cGC
  gcongr

/-- The second chosen factor lies within `cGC * √δ` of the identity. -/
theorem norm_gcChoice_snd_sub_one_le {U : SU2} {δ : ℝ}
    (hU : ‖(U : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ δ) (hδ : δ ≤ δGC) :
    ‖((gcChoice U).2 : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ cGC * Real.sqrt δ := by
  have h : ‖(U : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ δGC := hU.trans hδ
  simp only [gcChoice, h, ↓reduceDIte]
  refine ((exists_gc_eq le_rfl h).choose_spec.choose_spec.2.2).trans ?_
  unfold cGC
  gcongr

end SolovayKitaev
