/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.SolovayKitaev.GroupCommutator
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Cover

/-!
# The Solovay–Kitaev theorem for `SU(2)`

Words over a gate set `G` with an evaluation `ev : G → SU(2)` and an inversion `inv : G → G`
with `ev (inv g) = star (ev g)`. The Solovay–Kitaev recursion `skWord` improves a base
approximation: at level `k + 1` the residual `U w⁻¹` of the level-`k` word `w` is written as a
balanced group commutator `gc V W`, and `V`, `W` are replaced by their level-`k` words. The
length grows by the factor `5` per level and the error satisfies
`ε_{k+1} ≤ cSK ε_k ^ (3/2)` with `cSK = 8 cGC + 4 = 20`, so `cSK² ε_k ≤ (cSK² ε₀) ^ ((3/2) ^ k)`.
From an `ε₀`-net of words of length at most `L₀` with `ε₀ < 1 / cSK²`, every element of
`SU(2)` is within `ε` of a word of length `O (L₀ log ^ c (1 / ε))`, `c = log 5 / log (3/2)`.

## Main results

* `SolovayKitaev.length_skWord` — the level-`k` word has length at most `5 ^ k L₀`.
* `SolovayKitaev.dist_skWord_le` — the error bound of the recursion.
* `SolovayKitaev.solovay_kitaev` — **the Solovay–Kitaev theorem** for `SU(2)`.

## References

* C. M. Dawson, M. A. Nielsen, *The Solovay–Kitaev algorithm*, Quantum Inf. Comput. 6 (2006).
* M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information*, Appendix 3.
-/

@[expose] public section

set_option autoImplicit false

open Complex Matrix
open scoped Matrix.Norms.L2Operator

namespace SolovayKitaev

section Words

variable {G : Type*} (ev : G → SU2) (inv : G → G)

/-- The value in `SU(2)` of a word over the gate set `G`. -/
def wordEval (w : List G) : SU2 := (w.map ev).prod

/-- The inverse word: the reversed word of inverse letters. -/
def wordInv (w : List G) : List G := (w.map inv).reverse

/-- The inverse word has the length of the word. -/
@[simp] theorem length_wordInv (w : List G) : (wordInv inv w).length = w.length := by
  simp [wordInv]

/-- On an inverse-closed gate set, the inverse word evaluates to the adjoint. -/
theorem wordEval_wordInv (hinv : ∀ g, ev (inv g) = star (ev g)) (w : List G) :
    wordEval ev (wordInv inv w) = star (wordEval ev w) := by
  induction w with
  | nil => simp [wordEval, wordInv]
  | cons g w ih => simp_all [wordEval, wordInv, List.prod_append, star_mul]

/-- The word of the Solovay–Kitaev recursion at level `k` for `U`: at level `0` the base word,
at level `k + 1` the word `wV wW wV⁻¹ wW⁻¹ w` where `w` is the level-`k` word of `U`, the
pair `(V, W)` is the balanced commutator of `U w⁻¹`, and `wV`, `wW` are their level-`k`
words. -/
noncomputable def skWord (base : SU2 → List G) : ℕ → SU2 → List G
  | 0, U => base U
  | k + 1, U =>
    let w := skWord base k U
    let VW := gcChoice (U * star (wordEval ev w))
    skWord base k VW.1 ++ skWord base k VW.2 ++ wordInv inv (skWord base k VW.1) ++
      wordInv inv (skWord base k VW.2) ++ w

/-- The constant of the Solovay–Kitaev recursion: `ε_{k+1} ≤ cSK ε_k ^ (3/2)`. -/
def cSK : ℝ := 8 * cGC + 4

/-- The exponent `log 5 / log (3/2)` of the Solovay–Kitaev length bound. -/
noncomputable def skExp : ℝ := Real.log 5 / Real.log (3 / 2)

/-- The level-`k` word has length at most `5 ^ k L₀`. -/
theorem length_skWord (base : SU2 → List G) {L₀ : ℕ} (hb : ∀ U, (base U).length ≤ L₀)
    (k : ℕ) (U : SU2) : (skWord ev inv base k U).length ≤ 5 ^ k * L₀ := by
  induction k generalizing U with
  | zero => simpa [skWord] using hb U
  | succ k ih =>
    simp only [skWord, List.length_append, length_wordInv]
    have := ih U
    have := ih (gcChoice (U * star (wordEval ev (skWord ev inv base k U)))).1
    have := ih (gcChoice (U * star (wordEval ev (skWord ev inv base k U)))).2
    rw [pow_succ]
    grind

private lemma wordEval_append (a b : List G) :
    wordEval ev (a ++ b) = wordEval ev a * wordEval ev b := by
  simp [wordEval, List.prod_append]

private lemma cSK_eq : cSK = 20 := by
  unfold cSK cGC; norm_num

private lemma num_step (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 400) :
    8 * (2 * Real.sqrt x) * x + 4 * x ^ 2 ≤ 20 * (x * Real.sqrt x) := by
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 ≤ s ∧ x = s ^ 2 := ⟨Real.sqrt x, Real.sqrt_nonneg _,
    (Real.sq_sqrt h0).symm⟩
  rw [Real.sqrt_sq hs0]
  have : s ≤ 1 := by nlinarith
  nlinarith [pow_nonneg hs0 3, mul_nonneg (pow_nonneg hs0 3) (sub_nonneg.2 this)]

/-- One step of the recursion: if `Wd` is within `x` of `U` and `Va`, `Wa` are within `x` of the
factors of the balanced commutator of `U Wd⁻¹`, then `[Va, Wa] Wd` is within `20 x √x` of `U`. -/
private lemma sk_step (U Wd Va Wa : SU2) {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 400)
    (hU : ‖(U : Matrix (Fin 2) (Fin 2) ℂ) - Wd‖ ≤ x)
    (hV : ‖((gcChoice (U * star Wd)).1 : Matrix (Fin 2) (Fin 2) ℂ) - Va‖ ≤ x)
    (hW : ‖((gcChoice (U * star Wd)).2 : Matrix (Fin 2) (Fin 2) ℂ) - Wa‖ ≤ x) :
    ‖(U : Matrix (Fin 2) (Fin 2) ℂ) - (gc Va Wa * Wd)‖ ≤ 20 * (x * Real.sqrt x) := by
  have hWd : ‖(Wd : Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 := CStarRing.norm_of_mem_unitary Wd.2.1
  have hsWd : ‖(star (Wd : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1 := by rw [norm_star, hWd]
  have hss : star (Wd : Matrix (Fin 2) (Fin 2) ℂ) * Wd = 1 := Unitary.star_mul_self_of_mem Wd.2.1
  have hΔ : ‖((U * star Wd : SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1‖ ≤ x := by
    have e : ((U * star Wd : SU2) : Matrix (Fin 2) (Fin 2) ℂ) - 1 =
        ((U : Matrix (Fin 2) (Fin 2) ℂ) - Wd) * star (Wd : Matrix (Fin 2) (Fin 2) ℂ) := by
      have : ((Wd : Matrix (Fin 2) (Fin 2) ℂ)) * star (Wd : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
        Unitary.mul_star_self_of_mem Wd.2.1
      rw [Matrix.sub_mul, this]; rfl
    rw [e]
    exact (norm_mul_le _ _).trans (by rw [hsWd, mul_one]; exact hU)
  have hδ : x ≤ δGC := by unfold δGC; linarith
  have hd1 := norm_gcChoice_fst_sub_one_le hΔ hδ
  have hd2 := norm_gcChoice_snd_sub_one_le hΔ hδ
  have hsq : Real.sqrt x ≤ 1 / 20 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hc : cGC = 2 := rfl
  have key := norm_gc_sub_gc_le (V := ((gcChoice (U * star Wd)).1 : Matrix (Fin 2) (Fin 2) ℂ))
    (W := ((gcChoice (U * star Wd)).2 : Matrix (Fin 2) (Fin 2) ℂ)) (V' := Va) (W' := Wa)
    (d := 2 * Real.sqrt x) (Δ := x) (gcChoice (U * star Wd)).1.2.1 (gcChoice (U * star Wd)).2.2.1
    Va.2.1 Wa.2.1 (by rw [hc] at hd1; exact hd1) (by rw [hc] at hd2; exact hd2)
    (by linarith) hV hW
  have hU' := gc_gcChoice (U := U * star Wd) (hΔ.trans hδ)
  have e : (U : Matrix (Fin 2) (Fin 2) ℂ) - gc Va Wa * Wd =
      (gc (gcChoice (U * star Wd)).1 (gcChoice (U * star Wd)).2 - gc Va Wa) * Wd := by
    rw [← hU', Matrix.sub_mul]
    have : ((U * star Wd : SU2) : Matrix (Fin 2) (Fin 2) ℂ) * Wd = U := by
      change (U : Matrix (Fin 2) (Fin 2) ℂ) * star (Wd : Matrix (Fin 2) (Fin 2) ℂ) * Wd = U
      rw [Matrix.mul_assoc, hss, Matrix.mul_one]
    rw [this]
  rw [e]
  refine (norm_mul_le _ _).trans ?_
  rw [hWd, mul_one]
  exact key.trans (num_step x h0 h1)

/-- **Error of the Solovay–Kitaev recursion.** For a base approximation within
`ε₀ ≤ 1 / cSK²`, the level-`k` word is within `(cSK² ε₀) ^ ((3/2) ^ k) / cSK²`. -/
theorem dist_skWord_le (hinv : ∀ g, ev (inv g) = star (ev g)) (base : SU2 → List G) {ε₀ : ℝ}
    (hb : ∀ U : SU2, ‖(U : Matrix (Fin 2) (Fin 2) ℂ) - wordEval ev (base U)‖ ≤ ε₀)
    (hε₀ : ε₀ ≤ 1 / cSK ^ 2) (k : ℕ) (U : SU2) :
    ‖(U : Matrix (Fin 2) (Fin 2) ℂ) - wordEval ev (skWord ev inv base k U)‖ ≤
      (cSK ^ 2 * ε₀) ^ ((3 / 2 : ℝ) ^ k) / cSK ^ 2 := by
  rw [cSK_eq] at hε₀ ⊢
  have hε0 : 0 ≤ ε₀ := (norm_nonneg _).trans (hb 1)
  have hA0 : 0 ≤ (20 : ℝ) ^ 2 * ε₀ := by positivity
  have hA1 : (20 : ℝ) ^ 2 * ε₀ ≤ 1 := by
    rw [le_div_iff₀ (by norm_num)] at hε₀; linarith
  induction k generalizing U with
  | zero => simp only [skWord, pow_zero, Real.rpow_one]; linarith [hb U]
  | succ k ih =>
    set A : ℝ := (20 : ℝ) ^ 2 * ε₀ with hA
    set p : ℝ := (3 / 2 : ℝ) ^ k with hp
    have hp0 : 0 ≤ p := by positivity
    have hAp0 : 0 ≤ A ^ p := Real.rpow_nonneg hA0 _
    have hAp1 : A ^ p ≤ 1 := Real.rpow_le_one hA0 hA1 hp0
    have hx0 : 0 ≤ A ^ p / 20 ^ 2 := by positivity
    have hx1 : A ^ p / 20 ^ 2 ≤ 1 / 400 := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]; linarith
    have hstep := sk_step U (wordEval ev (skWord ev inv base k U))
      (wordEval ev (skWord ev inv base k (gcChoice (U * star (wordEval ev
        (skWord ev inv base k U)))).1))
      (wordEval ev (skWord ev inv base k (gcChoice (U * star (wordEval ev
        (skWord ev inv base k U)))).2)) hx0 hx1 (ih U) (ih _) (ih _)
    have hev : wordEval ev (skWord ev inv base (k + 1) U) =
        ((gc (wordEval ev (skWord ev inv base k (gcChoice (U * star (wordEval ev
          (skWord ev inv base k U)))).1) : Matrix (Fin 2) (Fin 2) ℂ)
          (wordEval ev (skWord ev inv base k (gcChoice (U * star (wordEval ev
          (skWord ev inv base k U)))).2) : Matrix (Fin 2) (Fin 2) ℂ)) *
          (wordEval ev (skWord ev inv base k U) : Matrix (Fin 2) (Fin 2) ℂ) :
          Matrix (Fin 2) (Fin 2) ℂ) := by
      simp only [skWord, wordEval_append, wordEval_wordInv ev inv hinv]
      rfl
    have hroot : Real.sqrt (A ^ p / 20 ^ 2) = Real.sqrt (A ^ p) / 20 := by
      rw [Real.sqrt_div hAp0, Real.sqrt_sq (by norm_num)]
    have hpow : A ^ ((3 / 2 : ℝ) ^ (k + 1)) = A ^ p * Real.sqrt (A ^ p) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hA0, ← Real.rpow_add' hA0 (by positivity)]
      congr 1
      rw [pow_succ]; ring
    rw [hev, hpow]
    refine hstep.trans (le_of_eq ?_)
    rw [hroot]
    ring

/-- **Solovay–Kitaev theorem for `SU(2)`.** Let the words of length at most `L₀` over an
inverse-closed gate set form an `ε₀`-net of `SU(2)` with `0 < ε₀ < 1 / cSK²`. Then every
`U ∈ SU(2)` is within `ε > 0` of a word of length at most
`5 L₀ · max 1 (log (1 / (cSK² ε)) / log (1 / (cSK² ε₀))) ^ (log 5 / log (3/2))`. -/
theorem solovay_kitaev (hinv : ∀ g, ev (inv g) = star (ev g)) {L₀ : ℕ} {ε₀ : NNReal}
    (hnet : Metric.IsCover ε₀ Set.univ (wordEval ev '' {w | w.length ≤ L₀}))
    (hε₀0 : 0 < ε₀) (hε₀ : (ε₀ : ℝ) < 1 / cSK ^ 2) (U : SU2) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : List G, ‖(U : Matrix (Fin 2) (Fin 2) ℂ) - wordEval ev w‖ ≤ ε ∧
      (w.length : ℝ) ≤ 5 * L₀ *
        max 1 (Real.log (1 / (cSK ^ 2 * ε)) / Real.log (1 / (cSK ^ 2 * ε₀))) ^ skExp := by
  rw [cSK_eq] at hε₀ ⊢
  have hnet' : ∀ V : SU2, ∃ w : List G, w.length ≤ L₀ ∧
      ‖(V : Matrix (Fin 2) (Fin 2) ℂ) - wordEval ev w‖ ≤ (ε₀ : ℝ) := by
    intro V
    have := hnet (Set.mem_univ V)
    obtain ⟨y, ⟨w, hw, rfl⟩, hy⟩ := this
    refine ⟨w, hw, ?_⟩
    have h2 : dist V (wordEval ev w) ≤ ε₀ := by
      have := (edist_le_coe).1 hy
      rw [dist_nndist]; exact_mod_cast this
    rw [Subtype.dist_eq, dist_eq_norm] at h2
    exact h2
  choose base hbl hbd using hnet'
  have hA0 : 0 < (20 : ℝ) ^ 2 * ε₀ := by positivity
  have hA1 : (20 : ℝ) ^ 2 * ε₀ < 1 := by
    rw [lt_div_iff₀ (by norm_num)] at hε₀; linarith
  have hB0 : 0 < (20 : ℝ) ^ 2 * ε := by positivity
  set A : ℝ := (20 : ℝ) ^ 2 * ε₀ with hA
  set B : ℝ := (20 : ℝ) ^ 2 * ε with hB
  set R : ℝ := max 1 (Real.log (1 / B) / Real.log (1 / A)) with hR
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := by linarith
  have hlogA : Real.log A < 0 := Real.log_neg hA0 hA1
  set x : ℝ := Real.log R / Real.log (3 / 2) with hx
  have hl32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hx0 : 0 ≤ x := div_nonneg (Real.log_nonneg hR1) hl32.le
  set k : ℕ := ⌈x⌉₊ with hk
  have hxk : x ≤ k := Nat.le_ceil x
  have hkx : (k : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hq : R ≤ (3 / 2 : ℝ) ^ k := by
    have : (3 / 2 : ℝ) ^ x = R := by
      rw [Real.rpow_def_of_pos (by norm_num), hx]
      rw [mul_div_cancel₀ _ hl32.ne', Real.exp_log hR0]
    rw [← this, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hxk
  have herr : (A ^ ((3 / 2 : ℝ) ^ k)) / 20 ^ 2 ≤ ε := by
    rw [div_le_iff₀ (by norm_num)]
    have hq0 : 0 ≤ (3 / 2 : ℝ) ^ k := by positivity
    rcases le_or_gt 1 B with hB1 | hB1
    · calc A ^ ((3 / 2 : ℝ) ^ k) ≤ 1 := Real.rpow_le_one hA0.le hA1.le hq0
        _ ≤ B := hB1
        _ = ε * 20 ^ 2 := by rw [hB]; ring
    · have hlogB : Real.log B < 0 := Real.log_neg hB0 hB1
      have h1 : Real.log (1 / B) / Real.log (1 / A) ≤ (3 / 2 : ℝ) ^ k :=
        (le_max_right _ _).trans hq
      rw [one_div, one_div, Real.log_inv, Real.log_inv, neg_div_neg_eq,
        div_le_iff_of_neg hlogA] at h1
      have : A ^ ((3 / 2 : ℝ) ^ k) ≤ B := by
        rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hA0 _) hB0, Real.log_rpow hA0]
        linarith
      calc _ ≤ B := this
        _ = ε * 20 ^ 2 := by rw [hB]; ring
  refine ⟨skWord ev inv base k U, ?_, ?_⟩
  · refine (dist_skWord_le ev inv hinv base (ε₀ := ε₀) hbd ?_ k U).trans ?_
    · rw [cSK_eq]; exact hε₀.le
    · rw [cSK_eq]; exact herr
  · have h5 : (5 : ℝ) ^ k ≤ 5 * R ^ skExp := by
      have e1 : (5 : ℝ) ^ x = R ^ skExp := by
        rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hR0, skExp, hx]; ring_nf
      calc (5 : ℝ) ^ k = (5 : ℝ) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
        _ ≤ (5 : ℝ) ^ (x + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hkx.le
        _ = 5 * R ^ skExp := by rw [Real.rpow_add (by norm_num), e1, Real.rpow_one]; ring
    have hlen : ((skWord ev inv base k U).length : ℝ) ≤ 5 ^ k * L₀ := by
      exact_mod_cast length_skWord ev inv base hbl k U
    calc _ ≤ 5 ^ k * (L₀ : ℝ) := hlen
      _ ≤ 5 * R ^ skExp * L₀ := by gcongr
      _ = _ := by ring

end Words

end SolovayKitaev
