/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Code
import CatCryptCore.Relational.Judgment
import Mathlib.Data.Real.Basic

/-!
# Cryptographic Advantage

This file defines the advantage of an adversary in distinguishing games.
-/

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational

open scoped ENNReal

/-- Probability that a computation returns true, starting from an initial heap.
    This sums over all final heaps. -/
noncomputable def prTrue (G : SPComp Bool) (h₀ : Heap) : ℝ≥0∞ :=
  ∑' h, (G h₀) (some (true, h))

/-- Advantage: distinguishing probability between two games,
    measured as the absolute difference of the probabilities of returning `true`.

    **Scope: the initial heap is fixed to `Heap.empty`.** This is the empty-heap
    distinguishing probability, *not* the supremum over all initial heaps; the
    stronger all-heap notion is `SDist.sdist`. The two are reconciled by the
    bridge lemmas `sdist_isPure_le` / `sdist_oracleGame_le` (`SDist.lean`), which
    bound this empty-heap advantage by the all-heap statistical distance. Use
    `Advantage` for empty-heap game hops; reach for `sdist` when the adversary
    may choose the starting state. -/
noncomputable def Advantage (G₀ G₁ : SPComp Bool) : ℝ≥0∞ :=
  -- Use empty initial heap as starting point
  -- Take max of (pr₀ - pr₁) and (pr₁ - pr₀) for unsigned difference
  let pr₀ := prTrue G₀ Heap.empty
  let pr₁ := prTrue G₁ Heap.empty
  (pr₀ - pr₁) ⊔ (pr₁ - pr₀)

/-- Advantage with explicit adversary -/
noncomputable def AdvantageA {α : Type*} (G₀ G₁ : SPComp α) (A : α → SPComp Bool) : ℝ≥0∞ :=
  Advantage (G₀.bind A) (G₁.bind A)

/-! ## Key Lemmas -/

/-- Helper: absolute difference in ENNReal satisfies triangle inequality.
    Using (a - b) ⊔ (b - a) as "absolute difference" for nonnegative numbers -/
private theorem abs_diff_triangle (a b c : ℝ≥0∞) :
    (a - c) ⊔ (c - a) ≤ ((a - b) ⊔ (b - a)) + ((b - c) ⊔ (c - b)) := by
  -- Key insight: (a - c) ≤ (a - b) + (b - c) in ENNReal (tsub_le_tsub_add_tsub)
  -- And similarly (c - a) ≤ (c - b) + (b - a)
  have h1 : a - c ≤ (a - b) + (b - c) := tsub_le_tsub_add_tsub
  have h2 : c - a ≤ (c - b) + (b - a) := tsub_le_tsub_add_tsub
  -- x ⊔ y ≤ z when both x ≤ z and y ≤ z
  apply max_le
  · -- a - c ≤ (a - b) ⊔ (b - a) + (b - c) ⊔ (c - b)
    calc a - c
        ≤ (a - b) + (b - c) := h1
      _ ≤ ((a - b) ⊔ (b - a)) + (b - c) :=
          add_le_add (le_max_left (a - b) (b - a)) le_rfl
      _ ≤ ((a - b) ⊔ (b - a)) + ((b - c) ⊔ (c - b)) :=
          add_le_add le_rfl (le_max_left (b - c) (c - b))
  · -- c - a ≤ (a - b) ⊔ (b - a) + (b - c) ⊔ (c - b)
    calc c - a
        ≤ (c - b) + (b - a) := h2
      _ ≤ ((c - b) ⊔ (b - c)) + (b - a) :=
          add_le_add (le_max_left (c - b) (b - c)) le_rfl
      _ = (b - a) + ((c - b) ⊔ (b - c)) := add_comm _ _
      _ ≤ ((b - a) ⊔ (a - b)) + ((c - b) ⊔ (b - c)) :=
          add_le_add (le_max_left (b - a) (a - b)) le_rfl
      _ = ((a - b) ⊔ (b - a)) + ((b - c) ⊔ (c - b)) := by
          rw [max_comm (b - a), max_comm (c - b)]

/-- Triangle inequality for advantage
    |Pr[G₀] - Pr[G₂]| ≤ |Pr[G₀] - Pr[G₁]| + |Pr[G₁] - Pr[G₂]| -/
@[grind] theorem advantage_triangle (G₀ G₁ G₂ : SPComp Bool) :
    Advantage G₀ G₂ ≤ Advantage G₀ G₁ + Advantage G₁ G₂ := by
  simp only [Advantage, abs_diff_triangle]

/-- The lifted eqPost relation is equivalent to Eq on pairs -/
private theorem lifted_eqPost_eq {α : Type*} :
    (fun (p₁ : α × Heap) (p₂ : α × Heap) => eqPost p₁.1 p₁.2 p₂.1 p₂.2) = Eq := by
  funext p₁ p₂
  simp only [eqPost, eq_iff_iff]
  constructor
  · intro ⟨ha, hh⟩; exact Prod.ext ha hh
  · intro h; rw [h]; exact ⟨rfl, rfl⟩

/-- Perfect indistinguishability from pRHL equality.
    If G₀ and G₁ produce equal outputs when started from equal heaps,
    no adversary can distinguish them. -/
theorem advantage_zero_of_rHoare {α : Type*} (G₀ G₁ : SPComp α)
    (h : rHoare eqPre G₀ G₁ eqPost) :
    ∀ A, AdvantageA G₀ G₁ A = 0 := by
  intro A
  -- Specialize h to empty heaps (which satisfy eqPre)
  have heq_pre : eqPre Heap.empty Heap.empty := rfl
  have h_lift := h Heap.empty Heap.empty heq_pre
  -- h_lift : liftR (lifted eqPost) (G₀ empty) (G₁ empty)
  -- The lifted relation is Eq by lifted_eqPost_eq
  rw [lifted_eqPost_eq] at h_lift
  -- h_lift : (G₀ empty) ⟨Eq⟩# (G₁ empty)
  -- By liftR_eq_implies_eq, the distributions are equal
  have h_distr_eq : G₀ Heap.empty = G₁ Heap.empty := liftR_eq_implies_eq h_lift
  -- Therefore the bound computations are also equal
  have h_bound_eq : (G₀.bind A) Heap.empty = (G₁.bind A) Heap.empty := by
    simp only [SPComp.bind_def, h_distr_eq]
  -- prTrue values are equal
  have h_pr_eq : prTrue (G₀.bind A) Heap.empty = prTrue (G₁.bind A) Heap.empty := by
    simp only [prTrue, h_bound_eq]
  -- Advantage is 0 when probabilities are equal
  simp only [AdvantageA, Advantage, h_pr_eq]
  -- (x - x) ⊔ (x - x) = 0 ⊔ 0 = 0
  simp only [tsub_self, max_self]

/-- Zero advantage from invariant-preserving judgment with state separation.

    If G₀ and G₁ preserve an invariant I and produce equal values,
    they are indistinguishable for any adversary that respects I.

    **Key Hypothesis:** `hA_respects` states that when two heaps are I-related,
    the adversary produces the same distribution. This captures the essence of
    state separation: the adversary cannot observe differences in protocol-internal
    state that is encapsulated by I.

    In CatCrypt/Rocq, this is enforced structurally via package validity:
    - A's locations `LA` are disjoint from protocol locations `L`
    - I only constrains locations in L
    - Therefore A cannot observe I-related differences (A only sees `LA`)

    For the basic case where I = eqPre (heap equality), use `advantage_zero_of_rHoare`. -/
theorem advantage_zero_of_inv {α : Type*} (I : RPre) (G₀ G₁ : SPComp α)
    (hI : I Heap.empty Heap.empty)
    (h : rHoare I G₀ G₁ (fun a₁ h₁ a₂ h₂ => a₁ = a₂ ∧ I h₁ h₂))
    (A : α → SPComp Bool)
    (hA_respects : ∀ a h₁ h₂, I h₁ h₂ → A a h₁ = A a h₂) :
    AdvantageA G₀ G₁ A = 0 := by
  -- The postcondition ensures a₁ = a₂ and I h₁ h₂
  -- By hA_respects, A a₁ h₁ = A a₁ h₂ = A a₂ h₂
  -- Therefore the distributions are equal and advantage is 0
  unfold AdvantageA Advantage prTrue
  -- Apply the rHoare judgment to get the coupling
  have hcoupling := h Heap.empty Heap.empty hI
  -- Prove the bound computations produce equal distributions
  have heq_distrs : (G₀ Heap.empty).bind (fun ⟨a, h'⟩ => A a h') =
                    (G₁ Heap.empty).bind (fun ⟨a, h'⟩ => A a h') := by
    -- Use liftR_eq_implies_eq: if coupled by Eq, then equal
    apply liftR_eq_implies_eq
    -- Compose the coupling from G₀, G₁ with the adversary
    apply liftR_bind hcoupling
    -- For related inputs, show A produces equal distributions
    intro p₁ p₂ hpost
    -- hpost : p₁.1 = p₂.1 ∧ I p₁.2 p₂.2
    obtain ⟨heq_a, hI_h⟩ := hpost
    -- p₁ = (a₁, h₁), p₂ = (a₂, h₂)
    -- heq_a : a₁ = a₂, hI_h : I h₁ h₂
    -- Need: (fun ⟨a, h'⟩ => A a h') p₁ ⟨Eq⟩# (fun ⟨a, h'⟩ => A a h') p₂
    -- i.e., A p₁.1 p₁.2 ⟨Eq⟩# A p₂.1 p₂.2
    -- Since a₁ = a₂ and I h₁ h₂, by hA_respects: A a₁ h₁ = A a₂ h₂
    simp only
    have hAeq : A p₁.1 p₁.2 = A p₂.1 p₂.2 := by
      rw [heq_a]
      exact hA_respects p₂.1 p₁.2 p₂.2 hI_h
    rw [hAeq]
    exact liftR_refl _
  -- Now the bound computations are equal
  simp only [SPComp.bind, heq_distrs, tsub_self]
  -- max 0 0 = 0
  simp only [max_self]

/-! ## Symmetry and Reflexivity -/

/-- Advantage is symmetric: swapping games doesn't change the advantage. -/
@[simp] theorem Advantage_sym (G₀ G₁ : SPComp Bool) :
    Advantage G₀ G₁ = Advantage G₁ G₀ := by
  simp only [Advantage, max_comm]

/-- Self-advantage is zero: no adversary can distinguish a game from itself. -/
@[simp] theorem Advantage_self (G : SPComp Bool) : Advantage G G = 0 := by
  simp only [Advantage, tsub_self, max_self]

/-! ## Utility Lemmas for Advantage Bounds -/

/-- Helper: sample Bool bind equates to SDistr.uniform bind -/
private theorem sample_bind_eq (A : Bool → SPComp Bool) (h₀ : Heap) :
    (SPComp.bind (SPComp.sample Bool) A) h₀ =
    (SDistr.uniform Bool).bind (fun b => A b h₀) := by
  simp only [SPComp.bind_def, SPComp.sample]
  rw [SDistr.bind_assoc]; congr 1; funext b; rw [SDistr.pure_bind]

/-- prTrue is at most 1 (probability bound). -/
@[grind] theorem prTrue_le_one (G : SPComp Bool) (h₀ : Heap) : prTrue G h₀ ≤ 1 := by
  unfold prTrue
  have hinj : Function.Injective (fun h : Heap => (some (true, h) : Option (Bool × Heap))) :=
    fun a b hab => congrArg Prod.snd (Option.some.inj hab)
  calc ∑' h, (G h₀) (some (true, h))
      ≤ ∑' (x : Option (Bool × Heap)), (G h₀) x :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj (G h₀)
    _ = 1 := (G h₀).tsum_coe

/-- prTrue of sampling Bool then applying A decomposes as weighted sum. -/
theorem prTrue_bind_sample_Bool (A : Bool → SPComp Bool) (h₀ : Heap) :
    prTrue (SPComp.bind (SPComp.sample Bool) A) h₀ =
    (2 : ℝ≥0∞)⁻¹ * prTrue (A true) h₀ + (2 : ℝ≥0∞)⁻¹ * prTrue (A false) h₀ := by
  unfold prTrue
  simp only [sample_bind_eq]
  simp only [SDistr.bind, PMF.bind_apply]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  rw [tsum_fintype, Fintype.sum_option]
  simp only [SDistr.uniform_apply_none, SDistr.uniform_apply_some, Fintype.card_bool,
             SDistr.fail_apply_some, ENNReal.tsum_eq_zero.mpr (fun _ => rfl), mul_zero, zero_add]
  rw [Fintype.sum_bool]
  simp [add_comm]

/-- Advantage of sampling uniform Bool vs pure constant is at most 1/2. -/
theorem advantage_sample_vs_pure_false (A : Bool → SPComp Bool) :
    AdvantageA (SPComp.sample Bool) (SPComp.pure false) A ≤ (2 : ℝ≥0∞)⁻¹ := by
  unfold AdvantageA Advantage
  rw [SPComp.pure_bind, prTrue_bind_sample_Bool]
  set p_t := prTrue (A true) Heap.empty
  set p_f := prTrue (A false) Heap.empty
  have hpt : p_t ≤ 1 := prTrue_le_one _ _
  have hpf : p_f ≤ 1 := prTrue_le_one _ _
  have hinv : (2 : ℝ≥0∞)⁻¹ ≤ 1 := ENNReal.inv_le_one.mpr (by norm_num)
  apply max_le
  · rw [tsub_le_iff_right]
    exact add_le_add
      (calc (2 : ℝ≥0∞)⁻¹ * p_t ≤ (2 : ℝ≥0∞)⁻¹ * 1 := by gcongr
        _ = _ := mul_one _)
      (mul_le_of_le_one_left (zero_le) hinv)
  · rw [tsub_le_iff_right]
    calc p_f = (2 : ℝ≥0∞)⁻¹ * p_f + (2 : ℝ≥0∞)⁻¹ * p_f := by
            rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
      _ ≤ (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ * p_f := by
          gcongr
          calc (2 : ℝ≥0∞)⁻¹ * p_f ≤ (2 : ℝ≥0∞)⁻¹ * 1 := by gcongr
            _ = _ := mul_one _
      _ ≤ (2 : ℝ≥0∞)⁻¹ + ((2 : ℝ≥0∞)⁻¹ * p_t + (2 : ℝ≥0∞)⁻¹ * p_f) := by
          gcongr; exact le_add_left le_rfl

/-! ## General Sampling Lemmas -/

/-- Generalized sample-bind equation for any finite nonempty type. -/
private theorem sample_bind_eq_general {α β : Type*} [Fintype α] [Nonempty α]
    (f : α → SPComp β) (h₀ : Heap) :
    (SPComp.bind (SPComp.sample α) f) h₀ =
    (SDistr.uniform α).bind (fun a => f a h₀) := by
  simp only [SPComp.bind_def, SPComp.sample]
  rw [SDistr.bind_assoc]; congr 1; funext a; rw [SDistr.pure_bind]

/-- prTrue of sampling then applying F decomposes as weighted sum over the sampled type. -/
theorem prTrue_bind_sample {α : Type*} [Fintype α] [Nonempty α]
    (F : α → SPComp Bool) (h₀ : Heap) :
    prTrue (SPComp.bind (SPComp.sample α) F) h₀ =
    ∑ x : α, (↑(Fintype.card α) : ℝ≥0∞)⁻¹ * prTrue (F x) h₀ := by
  unfold prTrue
  simp only [sample_bind_eq_general]
  simp only [SDistr.bind, PMF.bind_apply]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]
  rw [tsum_fintype, Fintype.sum_option]
  simp only [SDistr.uniform_apply_none, SDistr.uniform_apply_some,
             SDistr.fail_apply_some, ENNReal.tsum_eq_zero.mpr (fun _ => rfl), mul_zero, zero_add]

/-- Weighted sum bound: if each term is bounded, the weighted average is bounded.
    Used for proving that sampling from a common distribution preserves advantage bounds. -/
private theorem weighted_sum_le {α : Type*} [Fintype α] [Nonempty α]
    (p q : α → ℝ≥0∞) (ε : ℝ≥0∞)
    (h : ∀ x, p x ≤ q x + ε) :
    ∑ x : α, (↑(Fintype.card α) : ℝ≥0∞)⁻¹ * p x ≤
    (∑ x : α, (↑(Fintype.card α) : ℝ≥0∞)⁻¹ * q x) + ε := by
  set w := (↑(Fintype.card α) : ℝ≥0∞)⁻¹
  have hn0 : (↑(Fintype.card α) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp Fintype.card_pos)
  have hntop : (↑(Fintype.card α) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hnw : ↑(Fintype.card α) * w = 1 := ENNReal.mul_inv_cancel hn0 hntop
  have h1 : ∑ x, w * p x ≤ ∑ x, w * q x + ∑ _x : α, w * ε := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x _ => by rw [← mul_add]; gcongr; exact h x
  have h2 : ∑ _x : α, w * ε = ε := by
    rw [Finset.sum_const, Finset.card_univ]
    change ↑(Fintype.card α) • (w * ε) = ε
    rw [nsmul_eq_mul, ← mul_assoc, hnw, one_mul]
  calc ∑ x, w * p x ≤ (∑ x, w * q x) + ∑ _x : α, w * ε := h1
    _ = (∑ x, w * q x) + ε := by rw [h2]

/-- Advantage with uniform prefix sampling.

    If two games differ only in their continuation after sampling,
    and the continuation advantage is bounded for all sampled values,
    then the overall advantage is bounded.

    For finite types (like Word = Bool), this follows from the fact that
    sampling is a convex combination, and advantage respects convexity. -/
theorem advantageA_sample_bind {α β : Type*} [Fintype α] [Nonempty α]
    (f g : α → SPComp β) (A : β → SPComp Bool) (ε : ENNReal)
    (h : ∀ x, AdvantageA (f x) (g x) A ≤ ε) :
    AdvantageA (SPComp.bind (SPComp.sample α) f) (SPComp.bind (SPComp.sample α) g) A ≤ ε := by
  simp only [AdvantageA, Advantage, SPComp.bind_assoc]
  rw [prTrue_bind_sample, prTrue_bind_sample]
  -- Extract pointwise bounds from hypothesis
  have hfg : ∀ x, prTrue (SPComp.bind (f x) A) Heap.empty ≤
             prTrue (SPComp.bind (g x) A) Heap.empty + ε := by
    intro x
    have hx := h x; simp only [AdvantageA, Advantage] at hx
    have h1 := le_trans (le_max_left _ _) hx
    exact le_of_le_of_eq (tsub_le_iff_right.mp h1) (add_comm ε _)
  have hgf : ∀ x, prTrue (SPComp.bind (g x) A) Heap.empty ≤
             prTrue (SPComp.bind (f x) A) Heap.empty + ε := by
    intro x
    have hx := h x; simp only [AdvantageA, Advantage] at hx
    have h1 := le_trans (le_max_right _ _) hx
    exact le_of_le_of_eq (tsub_le_iff_right.mp h1) (add_comm ε _)
  apply max_le
  · exact tsub_le_iff_right.mpr (by rw [add_comm]; exact weighted_sum_le _ _ ε hfg)
  · exact tsub_le_iff_right.mpr (by rw [add_comm]; exact weighted_sum_le _ _ ε hgf)

/-! ## IsPure Prefix Factoring -/

/-- Factoring out an IsPure prefix from advantage bounds.

    If `pfx` is heap-independent and for every prefix value `x`, the advantage
    between `f x` and `g x` is bounded by `ε`, then the overall advantage
    is also bounded by `ε`.

    This is the key lemma for mechanizing HKDF hybrid steps where the
    differing game depends on the prefix output (e.g., `th_2` from keygens). -/
theorem advantageA_isPure_bind {α β : Type*}
    (pfx : SPComp α) (f g : α → SPComp β) (A : β → SPComp Bool) (ε : ℝ≥0∞)
    (hPure : SPComp.IsPure pfx)
    (h : ∀ x, AdvantageA (f x) (g x) A ≤ ε) :
    AdvantageA (pfx.bind f) (pfx.bind g) A ≤ ε := by
  obtain ⟨d, hd⟩ := hPure
  simp only [AdvantageA, SPComp.bind_assoc, Advantage]
  -- Key identity: (pfx.bind H) Heap.empty = d.bind(a => H a Heap.empty)
  have hbind : ∀ (H : α → SPComp Bool),
      (SPComp.bind pfx H) Heap.empty = d.bind (fun a => H a Heap.empty) := by
    intro H; simp only [SPComp.bind_def, hd, SDistr.bind_assoc, SDistr.pure_bind]
  -- Pointwise bounds from hypothesis (following advantageA_sample_bind pattern)
  have hfg : ∀ x, prTrue (SPComp.bind (f x) A) Heap.empty ≤
             prTrue (SPComp.bind (g x) A) Heap.empty + ε := by
    intro x
    have hx := h x; simp only [AdvantageA, Advantage] at hx
    have h1 := le_trans (le_max_left _ _) hx
    exact le_of_le_of_eq (tsub_le_iff_right.mp h1) (add_comm ε _)
  have hgf : ∀ x, prTrue (SPComp.bind (g x) A) Heap.empty ≤
             prTrue (SPComp.bind (f x) A) Heap.empty + ε := by
    intro x
    have hx := h x; simp only [AdvantageA, Advantage] at hx
    have h1 := le_trans (le_max_right _ _) hx
    exact le_of_le_of_eq (tsub_le_iff_right.mp h1) (add_comm ε _)
  -- Weight bound: ∑' a, d(some a) ≤ 1
  have hw : ∑' a, d (some a) ≤ 1 := by
    calc ∑' a, d (some a)
        ≤ ∑' oa, d oa := ENNReal.tsum_comp_le_tsum_of_injective (Option.some_injective _) d
      _ = 1 := d.tsum_coe
  -- Decompose prTrue as weighted sum over IsPure distribution
  have hprTrue : ∀ (H : α → SPComp Bool),
      prTrue (SPComp.bind pfx H) Heap.empty =
      ∑' a, d (some a) * prTrue (H a) Heap.empty := by
    intro H
    simp only [prTrue]
    simp_rw [hbind H]
    have bind_expand : ∀ bh : Bool × Heap,
        (d.bind (fun a => H a Heap.empty)) (some bh) =
        ∑' a, d (some a) * ((H a Heap.empty) (some bh)) := by
      intro bh
      simp only [SDistr.bind, PMF.bind_apply]
      exact SDistr.tsum_option_none_zero _
        (by simp only [SDistr.fail_apply_some, mul_zero])
    simp_rw [bind_expand]
    rw [ENNReal.tsum_comm]
    congr 1; funext a
    exact ENNReal.tsum_mul_left
  -- Helper: weighted tsum with sub-probability weights preserves bounds
  have weighted_bound : ∀ (P Q : α → ℝ≥0∞),
      (∀ x, P x ≤ Q x + ε) →
      ∑' a, d (some a) * P a ≤ (∑' a, d (some a) * Q a) + ε := by
    intro P Q hPQ
    calc ∑' a, d (some a) * P a
        ≤ ∑' a, d (some a) * (Q a + ε) :=
          ENNReal.tsum_le_tsum (fun a => by gcongr; exact hPQ a)
      _ = ∑' a, (d (some a) * Q a + d (some a) * ε) := by
          congr 1; funext a; exact mul_add _ _ _
      _ = (∑' a, d (some a) * Q a) + ∑' a, d (some a) * ε :=
          ENNReal.tsum_add
      _ = (∑' a, d (some a) * Q a) + (∑' a, d (some a)) * ε := by
          congr 1; exact ENNReal.tsum_mul_right
      _ ≤ (∑' a, d (some a) * Q a) + 1 * ε := by gcongr
      _ = (∑' a, d (some a) * Q a) + ε := by rw [one_mul]
  -- Bound the advantage
  rw [hprTrue (fun x => SPComp.bind (f x) A),
      hprTrue (fun x => SPComp.bind (g x) A)]
  apply max_le
  · exact tsub_le_iff_right.mpr (by rw [add_comm]; exact weighted_bound _ _ hfg)
  · exact tsub_le_iff_right.mpr (by rw [add_comm]; exact weighted_bound _ _ hgf)

end CatCrypt.Crypto
