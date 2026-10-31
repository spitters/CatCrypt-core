/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.PMFUniformDefs

/-!
# Expectations under `PMF.bind` and `PMF.map`, and uniform distributions

Mathlib candidates about expectations `∑' a, p a * g a` under `PMF.bind` and `PMF.map`,
uniform distributions on products and function spaces, and bounds on the probability of
an outcome of a bind.

## Main results

* `PMF.tsum_mul_comp_eq_map`, `PMF.tsum_bind_mul` — expectations under `map` and `bind`
* `PMF.uniform_prod_eq_bind`, `PMF.uniform_prod_fst_apply`, `PMF.uniform_prod_snd_apply`
  — the uniform distribution on a product samples the components independently
* `PMF.map_uniform_apply`, `PMF.map_uniform_pi_apply`, `PMF.map_uniform_pi_congr` — images
  of uniform distributions
* `PMF.tsum_map_guess_le` — a guess hits the image of `p` under `f` with probability at
  most the largest probability of a value of `f`
* `PMF.uniform_mem_list_le`, `PMF.uniform_box_le` — a uniform value lies in a list, and a
  uniform vector in a box
* `PMF.bind_map_true_le` — comparison of two binds by events on the support
* `PMF.indicator_le_mul_guess` — a uniform position among `q` hits the first occurrence
  of an entry with probability `1/q`
* `PMF.bind_apply_le_add_tsum`, `PMF.tsum_le_mul_bind_apply`, `PMF.bind_apply_le_of_le` —
  bounds on the probability of an outcome of a bind
* `PMF.uniformFintype_map_equiv` — the image of a uniform distribution under an
  equivalence is uniform
* `PMF.map_uniform_fst`, `PMF.map_uniform_prod_map`, `PMF.map_uniform_pi_of_map`,
  `PMF.map_uniform_comp_injective` — images of uniform pairs and uniform functions that
  are uniform
* `PMF.map_uniform_prod_fst`, `PMF.map_uniform_prod_snd`, `PMF.map_uniform_prod_pair_congr`,
  `PMF.map_uniform_prod_dep_congr` — maps of uniform pairs through one component, and their
  congruence under maps with equal image distributions

They belong in `Mathlib/Probability/ProbabilityMassFunction/Monad.lean` and
`Mathlib/Probability/Distributions/Uniform.lean`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

namespace PMF

section Uniform

variable {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] in
/-- An expectation over `p` of a function of `f` is the expectation over `p.map f`. -/
theorem tsum_mul_comp_eq_map (p : PMF A) (f : A → B) (g : B → ℝ≥0∞) :
    ∑' a, p a * g (f a) = ∑' b, (p.map f) b * g b := by
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (f a) (fun b hb => by simp [hb])]
  simp

/-- The uniform distribution on `A × B` samples the components independently. -/
theorem uniform_prod_eq_bind :
    PMF.uniformFintype (A × B) =
      (PMF.uniformFintype A).bind fun a => (PMF.uniformFintype B).map (Prod.mk a) := by
  ext ⟨a, b⟩
  rw [PMF.bind_apply, tsum_eq_single a]
  · rw [PMF.map_apply, tsum_eq_single b]
    · simp [PMF.uniformFintype_apply, Fintype.card_prod, ENNReal.mul_inv]
    · intro b' hb'; simp [Ne.symm hb']
  · intro a' ha'
    simp [PMF.map_apply, Ne.symm ha']

/-- Mapping the first component of a uniform pair by maps with equal image
distributions gives equal distributions. -/
theorem map_uniform_prod_fst_congr {A' C S : Type} [Fintype A'] [Nonempty A'] [Fintype S]
    [Nonempty S] {f : A → C} {g : A' → C}
    (h : (PMF.uniformFintype A).map f = (PMF.uniformFintype A').map g) :
    (PMF.uniformFintype (A × S)).map (fun ρ => (f ρ.1, ρ.2)) =
      (PMF.uniformFintype (A' × S)).map (fun ρ => (g ρ.1, ρ.2)) := by
  rw [uniform_prod_eq_bind, uniform_prod_eq_bind, PMF.map_bind, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have hf : ((PMF.uniformFintype A).bind fun a =>
      (PMF.uniformFintype S).map fun s => (f a, s)) =
      ((PMF.uniformFintype A).map f).bind fun c =>
        (PMF.uniformFintype S).map fun s => (c, s) := by
    rw [PMF.bind_map]; rfl
  have hg : ((PMF.uniformFintype A').bind fun a =>
      (PMF.uniformFintype S).map fun s => (g a, s)) =
      ((PMF.uniformFintype A').map g).bind fun c =>
        (PMF.uniformFintype S).map fun s => (c, s) := by
    rw [PMF.bind_map]; rfl
  rw [hf, hg, h]

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] in
/-- An expectation over `p.bind f` is the expectation over `p` of the expectations
over `f a`. -/
theorem tsum_bind_mul (p : PMF A) (f : A → PMF B) (g : B → ℝ≥0∞) :
    ∑' b, (p.bind f) b * g b = ∑' a, p a * ∑' b, f a b * g b := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

omit [Fintype B] [Nonempty B] in
/-- The image distribution of a uniform map at a point is the number of its
preimages over the size of the domain. -/
theorem map_uniform_apply [DecidableEq B] (f : A → B) (b : B) :
    ((PMF.uniformFintype A).map f) b =
      ((Finset.univ.filter fun a => f a = b).card : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹ := by
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformFintype_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 3
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact eq_comm

/-- The image distribution of a uniform function under a pointwise map is the product
of the image distributions of its coordinates. -/
theorem map_uniform_pi_apply {ι C : Type} [Fintype ι] [DecidableEq ι] [DecidableEq C]
    (f : ι → A → C) (o : ι → C) :
    ((PMF.uniformFintype (ι → A)).map fun r i => f i (r i)) o =
      ∏ i, ((PMF.uniformFintype A).map (f i)) (o i) := by
  rw [map_uniform_apply]
  simp only [map_uniform_apply]
  have hcard : (Finset.univ.filter fun r : ι → A => (fun i => f i (r i)) = o) =
      Fintype.piFinset fun i => Finset.univ.filter fun a => f i a = o i := by
    ext r
    simp [funext_iff]
  rw [hcard, Fintype.card_piFinset, Fintype.card_fun, Finset.prod_mul_distrib]
  push_cast
  congr 1
  rw [Finset.prod_const, Finset.card_univ, ENNReal.inv_pow]

/-- Mapping a uniform function pointwise by maps with equal image distributions gives
equal distributions. -/
theorem map_uniform_pi_congr {ι A' C : Type} [Fintype ι] [DecidableEq ι] [DecidableEq C]
    [Fintype A'] [Nonempty A'] (f : ι → A → C) (g : ι → A' → C)
    (h : ∀ i, (PMF.uniformFintype A).map (f i) = (PMF.uniformFintype A').map (g i)) :
    ((PMF.uniformFintype (ι → A)).map fun r i => f i (r i)) =
      ((PMF.uniformFintype (ι → A')).map fun r i => g i (r i)) := by
  ext o
  rw [map_uniform_pi_apply, map_uniform_pi_apply]
  simp only [h]

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] in
/-- A guess from a distribution `q` hits the image of `p` under `f` with probability at
most the largest probability of a value of `f`. -/
theorem tsum_map_guess_le (p : PMF A) (f : A → B) (q : PMF B) {ε : ℝ≥0∞}
    (h : ∀ b, p.toOuterMeasure {a | f a = b} ≤ ε) :
    ∑' a, p a * q (f a) ≤ ε := by
  rw [tsum_mul_comp_eq_map]
  calc ∑' b, (p.map f) b * q b ≤ ∑' b, ε * q b := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        gcongr
        rw [PMF.map_apply]
        refine le_of_eq_of_le ?_ (h b)
        rw [PMF.toOuterMeasure_apply]
        refine tsum_congr fun a => ?_
        by_cases hab : f a = b
        · simp [hab, Set.indicator]
        · simp only [Set.indicator, Set.mem_ofPred_eq, hab, ite_false]
          simp only [ite_eq_right_iff]
          intro h; exact absurd h.symm hab
    _ = ε := by rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

/-- The first component of a uniform pair lies in `S` with the uniform probability of
`S`. -/
theorem uniform_prod_fst_apply (S : Set A) :
    (PMF.uniformFintype (A × B)).toOuterMeasure {c | c.1 ∈ S} =
      (PMF.uniformFintype A).toOuterMeasure S := by
  have : (PMF.uniformFintype (A × B)).map Prod.fst = PMF.uniformFintype A := by
    rw [uniform_prod_eq_bind, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
    conv_lhs => arg 2; ext a; exact PMF.map_const (PMF.uniformFintype B) a
    exact PMF.bind_pure _
  rw [← this, PMF.toOuterMeasure_map_apply]
  rfl

/-- The second component of a uniform pair lies in `S` with the uniform probability of
`S`. -/
theorem uniform_prod_snd_apply (S : Set B) :
    (PMF.uniformFintype (A × B)).toOuterMeasure {c | c.2 ∈ S} =
      (PMF.uniformFintype B).toOuterMeasure S := by
  have : (PMF.uniformFintype (A × B)).map Prod.snd = PMF.uniformFintype B := by
    rw [uniform_prod_eq_bind, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
    exact ((PMF.uniformFintype A).bind_const _).trans (PMF.map_id _)
  rw [← this, PMF.toOuterMeasure_map_apply]
  rfl

/-- A uniform value lies in a list `l` with probability at most `|l| / |A|`. -/
theorem uniform_mem_list_le [DecidableEq A] (l : List A) :
    (PMF.uniformFintype A).toOuterMeasure {a | a ∈ l} ≤
      (l.length : ℝ≥0∞) * (Fintype.card A : ℝ≥0∞)⁻¹ := by
  rw [PMF.toOuterMeasure_uniformFintype_apply, div_eq_mul_inv]
  gcongr
  have : Fintype.card {a | a ∈ l} = l.toFinset.card := by
    rw [← Set.toFinset_card]; congr 1; ext a; simp
  rw [this]
  exact_mod_cast List.toFinset_card_le l

/-- A uniform vector in `Fin T → Fin (K + 1)` lies in a box whose sides each miss a
value with probability at most `(K/(K + 1))^T`. -/
theorem uniform_box_le (T K : ℕ) (S : Fin T → Finset (Fin (K + 1)))
    (hS : ∀ j, S j ≠ Finset.univ) :
    (PMF.uniformFintype (Fin T → Fin (K + 1))).toOuterMeasure {f | ∀ j, f j ∈ S j} ≤
      (K : ℝ≥0∞) ^ T / ((K : ℝ≥0∞) + 1) ^ T := by
  classical
  rw [PMF.toOuterMeasure_uniformFintype_apply]
  have hcard : Fintype.card {f : Fin T → Fin (K + 1) | ∀ j, f j ∈ S j} = ∏ j, (S j).card := by
    rw [← Fintype.card_piFinset]
    rw [← Set.toFinset_card]; congr 1; ext f; simp [Fintype.mem_piFinset]
  rw [hcard, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  gcongr
  · push_cast
    calc (∏ j, ((S j).card : ℝ≥0∞)) ≤ ∏ _j : Fin T, (K : ℝ≥0∞) := by
          gcongr with j
          have hlt : (S j).card < K + 1 := by
            have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr (hS j))
            simpa using this
          exact_mod_cast Nat.lt_succ_iff.mp hlt
      _ = (K : ℝ≥0∞) ^ T := by simp
  · push_cast; rfl

omit [Fintype A] [Nonempty A] in
/-- The image of `p` under `some` gives `some a` the mass of `a`. -/
theorem map_some_apply (p : PMF A) (a : A) : (p.map some) (some a) = p a := by
  rw [PMF.map_apply, tsum_eq_single a (fun b hb => by simp [Ne.symm hb])]
  simp

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] in
/-- An event `d x y` that implies the event `e x y` on the support of `p`, under two
families of distributions that agree on the support of `p`, has at most its
probability. -/
theorem bind_map_true_le (p : PMF A) (f g : A → PMF B) (d e : A → B → Bool)
    (h : ∀ x ∈ p.support, f x = g x ∧ ∀ y, d x y = true → e x y = true) :
    (p.bind fun x => (f x).map (d x)) true ≤ (p.bind fun x => (g x).map (e x)) true := by
  rw [PMF.bind_apply, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ p.support
  · obtain ⟨hfg, hde⟩ := h x hx
    rw [hfg]
    gcongr
    rw [PMF.map_apply, PMF.map_apply]
    refine ENNReal.tsum_le_tsum fun y => ?_
    by_cases hy : d x y = true
    · simp [hy, hde y hy]
    · simp only [Bool.not_eq_true] at hy
      simp [hy]
  · rw [PMF.apply_eq_zero_iff _ _ |>.mpr hx]
    simp

end Uniform

/-! ## Guessing a position and bounds on a bind -/

/-- `max q 1` is positive, so a uniform index below it is well defined. -/
instance maxOneNeZero (q : ℕ) : NeZero (max q 1) := ⟨by omega⟩

/-- A uniform position among `max q 1` hits the first occurrence of `s` in a list of at
most `q` entries with probability `1/q`: `q` times the probability that the entry at a
uniform position satisfies `f` is at least `1` whenever `s ∈ l` and `f s`. -/
theorem indicator_le_mul_guess {X : Type} [DecidableEq X] {q : ℕ} (l : List X) (s dflt : X)
    (hl : l.length ≤ q) (f : X → Bool) (hf : f s = true) :
    (if ∃ d ∈ l, d = s then (1 : ℝ≥0∞) else 0) ≤
      q * ((PMF.uniformFintype (Fin (max q 1))).map
        fun i : Fin (max q 1) => f (l.getD (i : ℕ) dflt)) true := by
  split_ifs with h
  · obtain ⟨d, hd, rfl⟩ := h
    obtain ⟨j, hj, hjd⟩ := List.getElem_of_mem hd
    have hq : max q 1 = q := by omega
    have hjq : j < max q 1 := by omega
    have hterm : (PMF.uniformFintype (Fin (max q 1))) ⟨j, hjq⟩ ≤
        ((PMF.uniformFintype (Fin (max q 1))).map
          fun i : Fin (max q 1) => f (l.getD (i : ℕ) dflt)) true := by
      rw [PMF.map_apply]
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum ⟨j, hjq⟩)
      simp [List.getElem?_eq_getElem hj, hjd, hf]
    calc (1 : ℝ≥0∞) = q * (q : ℝ≥0∞)⁻¹ :=
          (ENNReal.mul_inv_cancel (by exact_mod_cast (show q ≠ 0 by omega))
            (ENNReal.natCast_ne_top q)).symm
      _ ≤ _ := by
          gcongr
          refine le_trans (le_of_eq ?_) hterm
          simp [PMF.uniformFintype_apply, hq]
  · positivity

/-- A bind whose continuations `f x` give `b` probability at most that of `g x` plus
`h x` gives it probability at most the bind of `g` plus the expectation of `h`. -/
theorem bind_apply_le_add_tsum {X β : Type} (μ : PMF X) (f g : X → PMF β) (h : X → ℝ≥0∞)
    (b : β) (hfg : ∀ x, f x b ≤ g x b + h x) :
    (μ.bind f) b ≤ (μ.bind g) b + ∑' x, μ x * h x := by
  rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun x => by rw [← mul_add]; gcongr; exact hfg x

/-- An expectation of `h` is at most `c` times the probability of `b` under a bind whose
continuations `g x` give `b` probability at least `h x / c` on the support. -/
theorem tsum_le_mul_bind_apply {X β : Type} (μ : PMF X) (h : X → ℝ≥0∞) (g : X → PMF β)
    (c : ℝ≥0∞) (b : β) (hg : ∀ x, μ x ≠ 0 → h x ≤ c * g x b) :
    ∑' x, μ x * h x ≤ c * (μ.bind g) b := by
  rw [PMF.bind_apply, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : μ x = 0
  · simp [hx]
  · rw [mul_left_comm]
    gcongr
    exact hg x hx

/-- A bind whose continuations all give `b` probability at most `C` gives it probability
at most `C`. -/
theorem bind_apply_le_of_le {X β : Type} (μ : PMF X) (f : X → PMF β) (b : β) (C : ℝ≥0∞)
    (hf : ∀ x, f x b ≤ C) : (μ.bind f) b ≤ C := by
  rw [PMF.bind_apply]
  calc ∑' x, μ x * f x b ≤ ∑' x, μ x * C := ENNReal.tsum_le_tsum fun x => by gcongr; exact hf x
    _ = C := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The image of a uniform distribution under an equivalence is uniform. -/
theorem uniformFintype_map_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] (e : α ≃ β) : (PMF.uniformFintype α).map e = PMF.uniformFintype β := by
  classical
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b) fun a ha => by
    rw [ite_eq_right]; rintro rfl; exact ha (e.symm_apply_apply a).symm]
  simp [PMF.uniformFintype_apply, Fintype.card_congr e]

section UniformImage

variable {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]

/-- The first component of a uniform pair is uniform. -/
theorem map_uniform_fst :
    (PMF.uniformFintype (A × B)).map Prod.fst = PMF.uniformFintype A := by
  have h : ∀ a : A, PMF.map (fun _ : B => a) (PMF.uniformFintype B) = PMF.pure a :=
    fun a => PMF.map_const _ _
  rw [uniform_prod_eq_bind, PMF.map_bind]
  simp [PMF.map_comp, Function.comp_def, h]

/-- Maps taking uniform distributions to uniform distributions take a uniform pair to a
uniform pair. -/
theorem map_uniform_prod_map {C E : Type} [Fintype C] [Nonempty C] [Fintype E] [Nonempty E]
    {f : A → C} {g : B → E}
    (hf : (PMF.uniformFintype A).map f = PMF.uniformFintype C)
    (hg : (PMF.uniformFintype B).map g = PMF.uniformFintype E) :
    (PMF.uniformFintype (A × B)).map (Prod.map f g) = PMF.uniformFintype (C × E) := by
  rw [uniform_prod_eq_bind, uniform_prod_eq_bind, PMF.map_bind, ← hf, PMF.bind_map]
  refine congrArg _ (funext fun a => ?_)
  rw [← hg, PMF.map_comp, Function.comp_apply, PMF.map_comp]
  rfl

/-- A map taking the uniform distribution to the uniform distribution, applied pointwise,
takes a uniform function to a uniform function. -/
theorem map_uniform_pi_of_map {ι C : Type} [Fintype ι] [DecidableEq ι] [DecidableEq C]
    [Fintype C] [Nonempty C] {f : A → C}
    (hf : (PMF.uniformFintype A).map f = PMF.uniformFintype C) :
    (PMF.uniformFintype (ι → A)).map (fun r i => f (r i)) = PMF.uniformFintype (ι → C) := by
  rw [map_uniform_pi_congr (ι := ι) (fun _ => f) (fun _ => (id : C → C))
    (fun _ => by rw [hf, PMF.map_id])]
  exact PMF.map_id _

end UniformImage

/-- A uniform function on `D` composed with an injective `enc : I → D` is a uniform function
on `I`. -/
theorem map_uniform_comp_injective {D I R : Type} [Fintype D] [DecidableEq D] [Fintype I]
    [DecidableEq I] [Fintype R] [Nonempty R] {enc : I → D} (henc : Function.Injective enc) :
    (PMF.uniformFintype (D → R)).map (fun f => f ∘ enc) = PMF.uniformFintype (I → R) := by
  classical
  let E : (D → R) ≃ (I → R) × ({d // d ∉ Set.range enc} → R) :=
    ((Equiv.sumCompl (fun d => d ∈ Set.range enc)).symm.arrowCongr (Equiv.refl R)).trans
      ((Equiv.sumArrowEquivProdArrow _ _ R).trans
        (Equiv.prodCongr ((Equiv.ofInjective enc henc).symm.arrowCongr (Equiv.refl R))
          (Equiv.refl _)))
  have h1 : (PMF.uniformFintype (D → R)).map (fun f => f ∘ enc) =
      ((PMF.uniformFintype (D → R)).map E).map Prod.fst := by
    rw [PMF.map_comp]
    congr 1
  rw [h1, uniformFintype_map_equiv E, map_uniform_fst]

section UniformProdCongr

variable {A A' B B' C β : Type} [Fintype A] [Nonempty A] [Fintype A'] [Nonempty A']
  [Fintype B] [Nonempty B] [Fintype B'] [Nonempty B'] [Fintype C] [Nonempty C]

/-- A function of the first component of a uniform pair has the distribution of that function
of a uniform first component. -/
theorem map_uniform_prod_fst (f : A → β) :
    (PMF.uniformFintype (A × B)).map (fun p => f p.1) = (PMF.uniformFintype A).map f := by
  rw [← map_uniform_fst (A := A) (B := B), PMF.map_comp]
  rfl

/-- A function of the second component of a uniform pair has the distribution of that function
of a uniform second component. -/
theorem map_uniform_prod_snd (g : B → β) :
    (PMF.uniformFintype (A × B)).map (fun p => g p.2) = (PMF.uniformFintype B).map g := by
  rw [← uniformFintype_map_equiv (Equiv.prodComm B A), PMF.map_comp]
  exact map_uniform_prod_fst g

/-- Maps of the two components of a uniform pair with equal image distributions give equal
distributions of the pair of images. -/
theorem map_uniform_prod_pair_congr {X Y : Type} {f : A → X} {f' : A' → X} {g : B → Y}
    {g' : B' → Y} (hf : (PMF.uniformFintype A).map f = (PMF.uniformFintype A').map f')
    (hg : (PMF.uniformFintype B).map g = (PMF.uniformFintype B').map g') :
    (PMF.uniformFintype (A × B)).map (fun p => (f p.1, g p.2)) =
      (PMF.uniformFintype (A' × B')).map (fun p => (f' p.1, g' p.2)) := by
  have key : ∀ {A₁ B₁ : Type} [Fintype A₁] [Nonempty A₁] [Fintype B₁] [Nonempty B₁]
      (f₁ : A₁ → X) (g₁ : B₁ → Y),
      (PMF.uniformFintype (A₁ × B₁)).map (fun p => (f₁ p.1, g₁ p.2)) =
        ((PMF.uniformFintype A₁).map f₁).bind fun x =>
          ((PMF.uniformFintype B₁).map g₁).map (Prod.mk x) := by
    intro A₁ B₁ _ _ _ _ f₁ g₁
    rw [uniform_prod_eq_bind, PMF.map_bind, PMF.bind_map]
    refine congrArg _ (funext fun a => ?_)
    simp only [Function.comp_apply, PMF.map_comp]
    rfl
  rw [key, key, hf, hg]

/-- A function of a uniform `c` and of a map at `c` of an independent uniform `a` keeps its
distribution when, for every `c`, the map is replaced by one with the same image
distribution. -/
theorem map_uniform_prod_dep_congr {X : Type} (Φ : C → X → β) {f : C → A → X}
    {f' : C → A' → X}
    (hf : ∀ c, (PMF.uniformFintype A).map (f c) = (PMF.uniformFintype A').map (f' c)) :
    (PMF.uniformFintype (C × A)).map (fun p => Φ p.1 (f p.1 p.2)) =
      (PMF.uniformFintype (C × A')).map (fun p => Φ p.1 (f' p.1 p.2)) := by
  rw [uniform_prod_eq_bind, uniform_prod_eq_bind, PMF.map_bind, PMF.map_bind]
  refine congrArg _ (funext fun c => ?_)
  have h : ∀ {A₁ : Type} [Fintype A₁] [Nonempty A₁] (f₁ : C → A₁ → X),
      ((PMF.uniformFintype A₁).map (Prod.mk c)).map (fun p => Φ p.1 (f₁ p.1 p.2)) =
        ((PMF.uniformFintype A₁).map (f₁ c)).map (Φ c) := by
    intro A₁ _ _ f₁
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  rw [h, h, hf]

end UniformProdCongr

end PMF
