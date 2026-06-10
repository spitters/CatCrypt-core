/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Nominal.Fresh

/-!
# Name Abstraction

This file defines name abstraction `[𝔸]α` from Pitts' nominal sets (Chapter 4).
Name abstraction quotients `Atom × α` by "same up to fresh renaming", providing
the nominal analogue of alpha-equivalence for binders.

## Main definitions

* `AbsRel` - The equivalence relation: `(a, x) ~ (b, y)` iff for some fresh `c`,
  `swap a c • x = swap b c • y`
* `NameAbs α` - The quotient type `[𝔸]α = (Atom × α) / AbsRel`
* `abs a x` - The abstraction constructor
* `concretize` - Open an abstraction at a given fresh name

## Main results

* `abs_rename` - Key computation rule: `abs a x = abs b (swap a b • x)` when `b # x`
* `instMulActionNameAbs` - Permutation action: `π • abs a x = abs (π a) (π • x)`
* `instNomSetNameAbs` - Name abstraction forms a nominal set
* `concretize_abs` - Concretion inverts abstraction

## References

* [Pitts, *Nominal Sets*], Chapter 4
* [Benton et al., *Nominal SSProve*](https://eprint.iacr.org/2025/598)
-/

namespace CatCrypt.Nominal

/-! ## Key Tools -/

/-- Two permutations that agree on the support of `x` act the same on `x`. -/
theorem act_eq_of_agree_on_supp {α : Type*} [NomSet α] (π₁ π₂ : FinPerm) (x : α)
    (h : ∀ a ∈ NomSet.supp x, π₁ a = π₂ a) : π₁ • x = π₂ • x := by
  have : (π₂⁻¹ * π₁) • x = x := NomSet.act_eq_of_supp_fixed x _ (fun a ha => by
    simp only [FinPerm.mul_apply, FinPerm.inv_apply]
    rw [h a ha]; simp [FinPerm.apply_def])
  calc π₁ • x = π₂ • (π₂⁻¹ • (π₁ • x)) := by rw [smul_inv_smul]
    _ = π₂ • ((π₂⁻¹ * π₁) • x) := by rw [mul_smul]
    _ = π₂ • x := by rw [this]

/-- Conjugation identity for swaps through a permutation:
    `swap (π a) (π b) * π = π * swap a b`. -/
theorem swap_mul_comm (π : FinPerm) (a b : Atom) :
    FinPerm.swap (π a) (π b) * π = π * FinPerm.swap a b := by
  ext d
  simp only [FinPerm.mul_apply]
  by_cases hda : d = a
  · subst hda; simp
  · by_cases hdb : d = b
    · subst hdb; simp
    · rw [FinPerm.swap_apply_of_ne_of_ne hda hdb]
      have h1 : π d ≠ π a := fun h => hda (by simp [FinPerm.apply_def] at h; exact h)
      have h2 : π d ≠ π b := fun h => hdb (by simp [FinPerm.apply_def] at h; exact h)
      rw [FinPerm.swap_apply_of_ne_of_ne h1 h2]

/-- Conjugation of swap through a permutation on NomSet actions:
    `swap (π a) (π b) • (π • x) = π • (swap a b • x)`. -/
theorem swap_smul_conj {α : Type*} [NomSet α] (π : FinPerm) (a b : Atom) (x : α) :
    FinPerm.swap (π a) (π b) • (π • x) = π • (FinPerm.swap a b • x) := by
  rw [← mul_smul, ← mul_smul, swap_mul_comm]

/-- If `c # x` and `d # x`, then `swap a d • x = swap c d • (swap a c • x)`.
    Key tool for relating different fresh witnesses. -/
theorem swap_fresh_conj {α : Type*} [NomSet α] (a c d : Atom) (x : α)
    (hc : Fresh c x) (hd : Fresh d x) :
    FinPerm.swap a d • x = FinPerm.swap c d • (FinPerm.swap a c • x) := by
  rw [← mul_smul]
  apply act_eq_of_agree_on_supp
  intro y hy
  have hy_ne_c : y ≠ c := fun h => hc (h ▸ hy)
  have hy_ne_d : y ≠ d := fun h => hd (h ▸ hy)
  simp only [FinPerm.mul_apply]
  by_cases hya : y = a
  · subst hya; simp
  · rw [FinPerm.swap_apply_of_ne_of_ne hya hy_ne_c,
        FinPerm.swap_apply_of_ne_of_ne hy_ne_c hy_ne_d,
        FinPerm.swap_apply_of_ne_of_ne hya hy_ne_d]

/-- Freshness is preserved by permutation actions. -/
theorem fresh_act_of_fresh {α : Type*} [NomSet α] (π : FinPerm) (c : Atom) (x : α)
    (h : Fresh c x) : Fresh (π c) (π • x) := by
  intro hmem
  rw [NomSet.supp_act_eq_image, Finset.mem_image] at hmem
  obtain ⟨a, ha, hae⟩ := hmem
  have hac : a = c := by
    have := π.val.injective (show π.val a = π.val c from by exact_mod_cast hae)
    exact this
  exact h (hac ▸ ha)

/-! ## Section 1: Swap Conjugation -/

namespace FinPerm

/-- Swap conjugation: `(a b)(a c)(a b) = (b c)` when c ≠ a and c ≠ b. -/
theorem swap_conj (a b c : Atom) (hca : c ≠ a) (hcb : c ≠ b) :
    swap a b * swap a c * swap a b = swap b c := by
  apply FinPerm.val_injective; ext d
  simp only [mul_val, swap_val, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_def]
  split <;> split <;> split <;> simp_all [ne_comm]

end FinPerm

/-! ## Section 2: Equivalence Relation -/

/-- The name abstraction equivalence relation.
    Two pairs `(a, x)` and `(b, y)` are related if for some atom `c` fresh for both,
    `swap a c • x = swap b c • y`. -/
def AbsRel {α : Type*} [NomSet α] (p q : Atom × α) : Prop :=
  ∃ c : Atom, Fresh c (p, q) ∧ FinPerm.swap p.1 c • p.2 = FinPerm.swap q.1 c • q.2

namespace AbsRel

variable {α : Type*} [NomSet α]

/-- Decompose freshness for a nested pair `(p, q) : (Atom × α) × (Atom × α)`. -/
theorem fresh_pair (c : Atom) (p q : Atom × α)
    (h : Fresh c (p, q)) : c ≠ p.1 ∧ Fresh c p.2 ∧ c ≠ q.1 ∧ Fresh c q.2 := by
  unfold Fresh at h
  have h1 : c ∉ NomSet.supp p.1 := fun hm =>
    h (Finset.mem_union_left _ (Finset.mem_union_left _ hm))
  have h2 : c ∉ NomSet.supp p.2 := fun hm =>
    h (Finset.mem_union_left _ (Finset.mem_union_right _ hm))
  have h3 : c ∉ NomSet.supp q.1 := fun hm =>
    h (Finset.mem_union_right _ (Finset.mem_union_left _ hm))
  have h4 : c ∉ NomSet.supp q.2 := fun hm =>
    h (Finset.mem_union_right _ (Finset.mem_union_right _ hm))
  exact ⟨fun heq => h1 (heq ▸ Finset.mem_singleton_self _), h2,
         fun heq => h3 (heq ▸ Finset.mem_singleton_self _), h4⟩

/-- Build freshness for a nested pair from components. -/
theorem mk_fresh_pair (c : Atom) (p q : Atom × α)
    (h1 : c ≠ p.1) (h2 : Fresh c p.2) (h3 : c ≠ q.1) (h4 : Fresh c q.2) :
    Fresh c (p, q) := by
  intro hmem
  rcases Finset.mem_union.mp hmem with h | h
  · rcases Finset.mem_union.mp h with h' | h'
    · exact h1 (Finset.mem_singleton.mp h')
    · exact h2 h'
  · rcases Finset.mem_union.mp h with h' | h'
    · exact h3 (Finset.mem_singleton.mp h')
    · exact h4 h'

/-- AbsRel is reflexive. -/
theorem refl (p : Atom × α) : AbsRel p p := by
  refine ⟨freshFor p p, ?_, rfl⟩
  apply mk_fresh_pair
  · intro heq; exact freshFor_not_in_supp_left p p
      (heq ▸ Finset.mem_union_left _ (Finset.mem_singleton_self _))
  · exact fun hm => freshFor_not_in_supp_left p p (Finset.mem_union_right _ hm)
  · intro heq; exact freshFor_not_in_supp_right p p
      (heq ▸ Finset.mem_union_left _ (Finset.mem_singleton_self _))
  · exact fun hm => freshFor_not_in_supp_right p p (Finset.mem_union_right _ hm)

/-- AbsRel is symmetric. -/
theorem symm {p q : Atom × α} (h : AbsRel p q) : AbsRel q p := by
  obtain ⟨c, hfresh, heq⟩ := h
  have hf := fresh_pair c p q hfresh
  exact ⟨c, mk_fresh_pair c q p hf.2.2.1 hf.2.2.2 hf.1 hf.2.1, heq.symm⟩

/-- AbsRel is transitive. Uses `swap_fresh_conj` to unify witnesses. -/
theorem trans {p q r : Atom × α} (hpq : AbsRel p q) (hqr : AbsRel q r) : AbsRel p r := by
  obtain ⟨c₁, hf₁, heq₁⟩ := hpq
  obtain ⟨c₂, hf₂, heq₂⟩ := hqr
  have fp := fresh_pair c₁ p q hf₁
  have fq := fresh_pair c₂ q r hf₂
  let S := NomSet.supp (p, q) ∪ NomSet.supp (q, r) ∪ {c₁, c₂}
  let d := Atom.fresh S
  have hd : d ∉ S := Atom.fresh_not_mem S
  have hd_p1 : d ≠ p.1 := by
    intro h; apply hd; exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (h ▸ Finset.mem_singleton_self _))))
  have hd_p2 : Fresh d p.2 := by
    intro h; apply hd; exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  have hd_q1 : d ≠ q.1 := by
    intro h; apply hd; exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_left _
        (h ▸ Finset.mem_singleton_self _))))
  have hd_q2 : Fresh d q.2 := by
    intro h; apply hd; exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _ h)))
  have hd_r1 : d ≠ r.1 := by
    intro h; apply hd; exact Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _
        (h ▸ Finset.mem_singleton_self _))))
  have hd_r2 : Fresh d r.2 := by
    intro h; apply hd; exact Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _ h)))
  refine ⟨d, mk_fresh_pair d p r hd_p1 hd_p2 hd_r1 hd_r2, ?_⟩
  rw [swap_fresh_conj p.1 c₁ d p.2 fp.2.1 hd_p2]
  rw [heq₁]
  rw [← swap_fresh_conj q.1 c₁ d q.2 fp.2.2.2 hd_q2]
  rw [swap_fresh_conj q.1 c₂ d q.2 fq.2.1 hd_q2]
  rw [heq₂]
  rw [← swap_fresh_conj r.1 c₂ d r.2 fq.2.2.2 hd_r2]

end AbsRel

/-- The setoid for name abstraction. -/
def absRel_setoid (α : Type*) [NomSet α] : Setoid (Atom × α) where
  r := AbsRel
  iseqv := ⟨AbsRel.refl, fun h => AbsRel.symm h, fun h1 h2 => AbsRel.trans h1 h2⟩

/-! ## Section 3: NameAbs Quotient Type -/

/-- Name abstraction: the quotient of `Atom × α` by the equivalence
    "same up to fresh renaming". This is the nominal analogue of
    alpha-equivalence classes for binders (Pitts, Chapter 4).
    Defined as `abbrev` so instance search can see through it. -/
abbrev NameAbs (α : Type*) [NomSet α] := Quotient (absRel_setoid α)

scoped notation "[𝔸]" α => NameAbs α

/-- Construct a name abstraction from an atom and an element. -/
def abs {α : Type*} [NomSet α] (a : Atom) (x : α) : NameAbs α :=
  Quotient.mk (absRel_setoid α) (a, x)

/-! ## Section 4: Key Computation Rule -/

/-- The fundamental computation rule for name abstraction:
    `abs a x = abs b (swap a b • x)` when `b` is fresh for `x`. -/
theorem abs_rename {α : Type*} [NomSet α] (a : Atom) (x : α) (b : Atom)
    (hb : Fresh b x) (hba : b ≠ a) :
    abs a x = abs b (FinPerm.swap a b • x) := by
  apply Quotient.sound
  show AbsRel (a, x) (b, FinPerm.swap a b • x)
  let S := NomSet.supp x ∪ NomSet.supp (FinPerm.swap a b • x) ∪ {a, b}
  let c := Atom.fresh S
  have hc : c ∉ S := Atom.fresh_not_mem S
  have hc_ne_a : c ≠ a := by
    intro h; apply hc; exact Finset.mem_union_right _ (h ▸ Finset.mem_insert_self _ _)
  have hc_ne_b : c ≠ b := by
    intro h; apply hc; exact Finset.mem_union_right _
      (Finset.mem_insert_of_mem (h ▸ Finset.mem_singleton_self _))
  have hc_x : Fresh c x := by
    intro h; apply hc; exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
  have hc_swapped : Fresh c (FinPerm.swap a b • x) := by
    intro h; apply hc; exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
  refine ⟨c, AbsRel.mk_fresh_pair c (a, x) (b, FinPerm.swap a b • x)
    hc_ne_a hc_x hc_ne_b hc_swapped, ?_⟩
  rw [← mul_smul]
  apply act_eq_of_agree_on_supp
  intro y hy
  have hy_ne_b : y ≠ b := fun h => hb (h ▸ hy)
  have hy_ne_c : y ≠ c := fun h => hc_x (h ▸ hy)
  simp only [FinPerm.mul_apply]
  by_cases hya : y = a
  · subst hya; simp
  · rw [FinPerm.swap_apply_of_ne_of_ne hya hy_ne_b,
        FinPerm.swap_apply_of_ne_of_ne hy_ne_b hy_ne_c,
        FinPerm.swap_apply_of_ne_of_ne hya hy_ne_c]

/-! ## Section 5: Permutation Action -/

/-- Permutations preserve the abstraction equivalence relation. -/
theorem AbsRel_act {α : Type*} [NomSet α] (π : FinPerm) {p q : Atom × α}
    (h : AbsRel p q) : AbsRel (π • p.1, π • p.2) (π • q.1, π • q.2) := by
  obtain ⟨c, hfresh, heq⟩ := h
  have hf := AbsRel.fresh_pair c p q hfresh
  refine ⟨π c, ?_, ?_⟩
  · apply AbsRel.mk_fresh_pair
    · exact fun h => hf.1 (π.val.injective (by exact_mod_cast h))
    · exact fresh_act_of_fresh π c p.2 hf.2.1
    · exact fun h => hf.2.2.1 (π.val.injective (by exact_mod_cast h))
    · exact fresh_act_of_fresh π c q.2 hf.2.2.2
  · dsimp only [Prod.fst, Prod.snd]
    change FinPerm.swap (π p.1) (π c) • (π • p.2) =
           FinPerm.swap (π q.1) (π c) • (π • q.2)
    rw [swap_smul_conj, swap_smul_conj, heq]

/-- MulAction instance for NameAbs: `π • abs a x = abs (π a) (π • x)`. -/
noncomputable instance instMulActionNameAbs {α : Type*} [NomSet α] :
    MulAction FinPerm (NameAbs α) where
  smul := fun π => Quotient.map (fun p => (π • p.1, π • p.2))
    (fun _ _ h => AbsRel_act π h)
  one_smul := fun q => Quotient.inductionOn q fun p => by
    simp only [HSMul.hSMul, SMul.smul, Quotient.map_mk]
    congr 1
    exact Prod.ext (by simp [FinPerm.apply_def]) (one_smul _ _)
  mul_smul := fun π₁ π₂ q => Quotient.inductionOn q fun p => by
    simp only [HSMul.hSMul, SMul.smul, Quotient.map_mk]
    congr 1
    exact Prod.ext (by simp [FinPerm.apply_def]) (mul_smul _ _ _)

@[simp]
theorem smul_abs {α : Type*} [NomSet α] (π : FinPerm) (a : Atom) (x : α) :
    π • abs a x = abs (π • a) (π • x) := rfl

/-! ## Section 6: NomSet Instance -/

/-- Support of a name abstraction representative: `supp x \ {a}`. -/
private noncomputable def absSupp {α : Type*} [NomSet α] (p : Atom × α) : Finset Atom :=
  NomSet.supp p.2 \ {p.1}

/-- AbsRel-related pairs have the same support. -/
private theorem absSupp_eq_of_absRel {α : Type*} [NomSet α] {p q : Atom × α}
    (h : AbsRel p q) : absSupp p = absSupp q := by
  obtain ⟨c, hfresh, heq⟩ := h
  have hf := AbsRel.fresh_pair c p q hfresh
  ext a
  simp only [absSupp, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · intro ⟨ha_in, ha_ne⟩
    have ha_ne_c : a ≠ c := fun h => hf.2.1 (h ▸ ha_in)
    have : a ∈ NomSet.supp (FinPerm.swap p.1 c • p.2) := by
      rw [NomSet.supp_act_eq_image, Finset.mem_image]
      exact ⟨a, ha_in, FinPerm.swap_apply_of_ne_of_ne ha_ne ha_ne_c⟩
    rw [heq] at this
    rw [NomSet.supp_act_eq_image, Finset.mem_image] at this
    obtain ⟨b, hb_in, hb_eq⟩ := this
    by_cases hbq : b = q.1
    · exfalso; rw [hbq, FinPerm.swap_apply_left] at hb_eq; exact ha_ne_c hb_eq.symm
    · by_cases hbc : b = c
      · exfalso; exact hf.2.2.2 (hbc ▸ hb_in)
      · rw [FinPerm.swap_apply_of_ne_of_ne hbq hbc] at hb_eq
        exact ⟨hb_eq ▸ hb_in, fun h => hbq (hb_eq ▸ h)⟩
  · intro ⟨ha_in, ha_ne⟩
    have ha_ne_c : a ≠ c := fun h => hf.2.2.2 (h ▸ ha_in)
    have : a ∈ NomSet.supp (FinPerm.swap q.1 c • q.2) := by
      rw [NomSet.supp_act_eq_image, Finset.mem_image]
      exact ⟨a, ha_in, FinPerm.swap_apply_of_ne_of_ne ha_ne ha_ne_c⟩
    rw [← heq] at this
    rw [NomSet.supp_act_eq_image, Finset.mem_image] at this
    obtain ⟨b, hb_in, hb_eq⟩ := this
    by_cases hbp : b = p.1
    · exfalso; rw [hbp, FinPerm.swap_apply_left] at hb_eq; exact ha_ne_c hb_eq.symm
    · by_cases hbc : b = c
      · exfalso; exact hf.2.1 (hbc ▸ hb_in)
      · rw [FinPerm.swap_apply_of_ne_of_ne hbp hbc] at hb_eq
        exact ⟨hb_eq ▸ hb_in, fun h => hbp (hb_eq ▸ h)⟩

/-- NomSet instance for NameAbs. -/
noncomputable instance instNomSetNameAbs {α : Type*} [NomSet α] :
    NomSet (NameAbs α) where
  toMulAction := instMulActionNameAbs
  supp := fun q => q.lift (fun p => absSupp p) (fun _ _ h => absSupp_eq_of_absRel h)
  supp_supports := fun q π hfix => by
    obtain ⟨p, rfl⟩ := q.exists_rep
    simp only [Quotient.lift_mk] at hfix
    show π • Quotient.mk _ p = Quotient.mk _ p
    simp only [HSMul.hSMul, SMul.smul, Quotient.map_mk]
    apply Quotient.sound
    show AbsRel (π • p.1, π • p.2) p
    set S := NomSet.supp p ∪ NomSet.supp (π • p.1, π • p.2) with hS_def
    set c := Atom.fresh S with hc_def
    have hc_not_S : c ∉ S := Atom.fresh_not_mem S
    have hc_fresh_p : c ∉ NomSet.supp p := fun h => hc_not_S (Finset.mem_union_left _ h)
    have hc_fresh_πp : c ∉ NomSet.supp (π • p.1, π • p.2) :=
      fun h => hc_not_S (Finset.mem_union_right _ h)
    refine ⟨c, ?_, ?_⟩
    · apply AbsRel.mk_fresh_pair
      · intro h; apply hc_fresh_πp; apply Finset.mem_union_left
        rw [h]; exact Finset.mem_singleton_self _
      · intro h; exact hc_fresh_πp (Finset.mem_union_right _ h)
      · intro h; apply hc_fresh_p; apply Finset.mem_union_left
        rw [h]; exact Finset.mem_singleton_self _
      · intro h; exact hc_fresh_p (Finset.mem_union_right _ h)
    · have hc_ne_p1 : c ≠ p.1 := by
        intro h; apply hc_fresh_p; apply Finset.mem_union_left
        rw [h]; exact Finset.mem_singleton_self _
      have hc_fresh_p2 : Fresh c p.2 := fun h => hc_fresh_p (Finset.mem_union_right _ h)
      have hπ_fix : ∀ a ∈ NomSet.supp p.2, a ≠ p.1 → π a = a := by
        intro a ha ha_ne
        exact hfix a (Finset.mem_sdiff.mpr ⟨ha, Finset.notMem_singleton.mpr ha_ne⟩)
      dsimp only [Prod.fst, Prod.snd]
      rw [← mul_smul]
      apply act_eq_of_agree_on_supp
      intro a ha
      have ha_ne_c : a ≠ c := fun h => hc_fresh_p2 (h ▸ ha)
      simp only [FinPerm.mul_apply]
      by_cases ha_p1 : a = p.1
      · subst ha_p1
        rw [FinPerm.swap_apply_left]
        rw [show π.apply p.1 = π • p.1 from rfl, FinPerm.swap_apply_left]
      · have hπa := hπ_fix a ha ha_p1
        rw [hπa, FinPerm.swap_apply_of_ne_of_ne ha_p1 ha_ne_c]
        have ha_ne_πp1 : a ≠ π p.1 := by
          intro heq; apply ha_p1
          have h1 : π.val a = a := by rw [show π.val a = π a from rfl]; exact hπa
          have h2 : π.val p.1 = a := by rw [show π.val p.1 = π p.1 from rfl]; exact heq.symm
          exact π.val.injective (h1.trans h2.symm)
        exact FinPerm.swap_apply_of_ne_of_ne ha_ne_πp1 ha_ne_c
  supp_equivariant := fun q π => Quotient.inductionOn q fun p => by
    simp only [HSMul.hSMul, SMul.smul, Quotient.map_mk, Quotient.lift_mk]
    show absSupp (π • p.1, π • p.2) = (absSupp p).image (π ·)
    unfold absSupp
    rw [show (π • p.1, π • p.2).2 = π • p.2 from rfl,
        show (π • p.1, π • p.2).1 = π • p.1 from rfl]
    rw [NomSet.supp_act_eq_image]
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_singleton]
    constructor
    · intro ⟨⟨b, hb, hba⟩, ha_ne⟩
      exact ⟨b, ⟨hb, fun hbp => ha_ne (hba ▸ show π b = π p.1 from congr_arg (π ·) hbp)⟩, hba⟩
    · intro ⟨b, ⟨hb_in, hb_ne⟩, hba⟩
      refine ⟨⟨b, hb_in, hba⟩, fun h => hb_ne ?_⟩
      have : π b = π p.1 := by exact_mod_cast (hba ▸ h)
      exact π.val.injective this

/-! ## Section 7: Some-Any Property & Concretion -/

/-- The "some-any" property: if AbsRel holds with one fresh witness,
    it holds with any fresh witness. -/
theorem absRel_any_fresh {α : Type*} [NomSet α] {p q : Atom × α}
    (h : AbsRel p q) (d : Atom) (hd : Fresh d (p, q)) :
    FinPerm.swap p.1 d • p.2 = FinPerm.swap q.1 d • q.2 := by
  obtain ⟨c, hfresh, heq⟩ := h
  have hf := AbsRel.fresh_pair c p q hfresh
  have hfd := AbsRel.fresh_pair d p q hd
  rw [swap_fresh_conj p.1 c d p.2 hf.2.1 hfd.2.1]
  rw [heq]
  rw [← swap_fresh_conj q.1 c d q.2 hf.2.2.2 hfd.2.2.2]

/-- Well-definedness of concretion: if AbsRel p q and `a` is fresh for the abstraction
    class (i.e. `a ∉ absSupp p`), then `swap a p.1 • p.2 = swap a q.1 • q.2`. -/
private theorem concretize_wd {α : Type*} [NomSet α] (a : Atom) {p q : Atom × α}
    (hpq : AbsRel p q) (ha : a ∉ absSupp p) :
    FinPerm.swap a p.1 • p.2 = FinPerm.swap a q.1 • q.2 := by
  obtain ⟨a₁, x₁⟩ := p
  obtain ⟨a₂, x₂⟩ := q
  have ha_q : a ∉ absSupp (a₂, x₂) := absSupp_eq_of_absRel hpq ▸ ha
  simp only [absSupp, Finset.mem_sdiff, Finset.mem_singleton, not_and, not_not] at ha ha_q
  obtain ⟨c, hfresh, heq⟩ := hpq
  have hf := AbsRel.fresh_pair c (a₁, x₁) (a₂, x₂) hfresh
  by_cases hap : a = a₁
  · subst hap -- a₁ eliminated, replaced by a
    simp only [FinPerm.swap_self, one_smul]
    by_cases haq : a = a₂
    · subst haq -- a₂ eliminated, replaced by a
      rw [FinPerm.swap_self, one_smul]
      have := congr_arg ((FinPerm.swap a c)⁻¹ • ·) heq
      simp only [inv_smul_smul] at this
      exact this
    · have ha_not_x₂ : a ∉ NomSet.supp x₂ := fun h => haq (ha_q h)
      have h1 : x₁ = FinPerm.swap a c • (FinPerm.swap a₂ c • x₂) := by
        rw [← heq, ← mul_smul, FinPerm.swap_swap, one_smul]
      rw [h1, ← mul_smul]; apply act_eq_of_agree_on_supp
      intro y hy
      have hy_ne_a : y ≠ a := fun h => ha_not_x₂ (h ▸ hy)
      have hy_ne_c : y ≠ c := fun h => hf.2.2.2 (h ▸ hy)
      simp only [FinPerm.mul_apply]
      by_cases hya₂ : y = a₂
      · subst hya₂; simp
      · rw [FinPerm.swap_apply_of_ne_of_ne hya₂ hy_ne_c,
            FinPerm.swap_apply_of_ne_of_ne hy_ne_a hy_ne_c,
            FinPerm.swap_apply_of_ne_of_ne hy_ne_a hya₂]
  · by_cases haq : a = a₂
    · subst haq -- a₂ eliminated, replaced by a
      have ha_not_x₁ : a ∉ NomSet.supp x₁ := fun h => hap (ha h)
      simp only [FinPerm.swap_self, one_smul]; symm
      have h1 : x₂ = FinPerm.swap a c • (FinPerm.swap a₁ c • x₁) := by
        rw [heq, ← mul_smul, FinPerm.swap_swap, one_smul]
      rw [h1, ← mul_smul]; apply act_eq_of_agree_on_supp
      intro y hy
      have hy_ne_a : y ≠ a := fun h => ha_not_x₁ (h ▸ hy)
      have hy_ne_c : y ≠ c := fun h => hf.2.1 (h ▸ hy)
      simp only [FinPerm.mul_apply]
      by_cases hya₁ : y = a₁
      · subst hya₁; simp
      · rw [FinPerm.swap_apply_of_ne_of_ne hya₁ hy_ne_c,
            FinPerm.swap_apply_of_ne_of_ne hy_ne_a hy_ne_c,
            FinPerm.swap_apply_of_ne_of_ne hy_ne_a hya₁]
    · have ha_not_x₁ : a ∉ NomSet.supp x₁ := fun h => hap (ha h)
      have ha_not_x₂ : a ∉ NomSet.supp x₂ := fun h => haq (ha_q h)
      have ha_fresh : Fresh a ((a₁, x₁), (a₂, x₂)) :=
        AbsRel.mk_fresh_pair a (a₁, x₁) (a₂, x₂) hap ha_not_x₁ haq ha_not_x₂
      rw [FinPerm.swap_comm a a₁, FinPerm.swap_comm a a₂]
      exact absRel_any_fresh ⟨c, hfresh, heq⟩ a ha_fresh

/-- Concretize a name abstraction at atom `a`: open `abs b x` as `swap a b • x`.
    Uses `Quotient.out` for the definition; meaningful when `a # nabs`. -/
noncomputable def concretize {α : Type*} [NomSet α] (a : Atom)
    (nabs : NameAbs α) : α :=
  FinPerm.swap a nabs.out.1 • nabs.out.2

/-- Concretize applied to an abstraction. -/
theorem concretize_abs {α : Type*} [NomSet α] (a b : Atom) (x : α)
    (ha : Fresh a (abs b x)) : concretize a (abs b x) = FinPerm.swap a b • x := by
  unfold concretize
  have hrel : AbsRel (abs b x).out (b, x) :=
    Quotient.mk_out (s := absRel_setoid α) (b, x)
  exact concretize_wd a hrel (by
    have hsup : absSupp (abs b x).out = absSupp (b, x) := absSupp_eq_of_absRel hrel
    rw [hsup]
    show a ∉ absSupp (b, x)
    exact ha)

/-- Concretize applied to an abstraction where `a` matches. -/
theorem concretize_abs_self {α : Type*} [NomSet α] (a : Atom) (x : α)
    (ha : Fresh a (abs a x)) : concretize a (abs a x) = x := by
  rw [concretize_abs a a x ha, FinPerm.swap_self, one_smul]

/-! ## Section 8: Equivariance & Functorial Map -/

/-- An equivariant function preserves the permutation action. -/
def Equivariant {α β : Type*} [MulAction FinPerm α] [MulAction FinPerm β] (f : α → β) : Prop :=
  ∀ π : FinPerm, ∀ x : α, f (π • x) = π • f x

/-- Support inclusion for equivariant functions. -/
theorem supp_sub_of_equivariant {α β : Type*} [NomSet α] [NomSet β]
    (f : α → β) (hf : Equivariant f) (x : α) :
    NomSet.supp (f x) ⊆ NomSet.supp x := by
  intro a ha
  by_contra h_not
  let b := freshFor x (f x)
  have hb_x : Fresh b x := freshFor_not_in_supp_left x (f x)
  have hb_fx : Fresh b (f x) := freshFor_not_in_supp_right x (f x)
  have h1 : FinPerm.swap a b • x = x :=
    Fresh.act_swap_fresh a b x (fun h => h_not h) hb_x
  have h2 : FinPerm.swap a b • f x = f x := by rw [← hf, h1]
  have h3 : NomSet.supp (f x) = (NomSet.supp (f x)).image (FinPerm.swap a b ·) := by
    conv_lhs => rw [show f x = FinPerm.swap a b • f x from h2.symm]
    rw [NomSet.supp_act_eq_image]
  have hb_in : b ∈ NomSet.supp (f x) := by
    rw [h3, Finset.mem_image]
    exact ⟨a, ha, FinPerm.swap_apply_left a b⟩
  exact hb_fx hb_in

/-- Functorial map on name abstractions: lift an equivariant function. -/
noncomputable def NameAbs.map {α β : Type*} [NomSet α] [NomSet β]
    (f : α → β) (hf : Equivariant f) : NameAbs α → NameAbs β :=
  Quotient.map (fun p => (p.1, f p.2)) (by
    intro p q ⟨c, hfresh, heq⟩
    have hf_pair := AbsRel.fresh_pair c p q hfresh
    refine ⟨c, ?_, ?_⟩
    · apply AbsRel.mk_fresh_pair
      · exact hf_pair.1
      · exact fun h => hf_pair.2.1 (supp_sub_of_equivariant f hf p.2 h)
      · exact hf_pair.2.2.1
      · exact fun h => hf_pair.2.2.2 (supp_sub_of_equivariant f hf q.2 h)
    · rw [← hf, ← hf, heq])

theorem NameAbs.map_abs {α β : Type*} [NomSet α] [NomSet β]
    (f : α → β) (hf : Equivariant f) (a : Atom) (x : α) :
    NameAbs.map f hf (abs a x) = abs a (f x) := by
  simp [NameAbs.map, abs, Quotient.map_mk]

end CatCrypt.Nominal
