/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Nominal.Nominal

/-!
# Fresh Atoms and the Move Operation

This file defines freshness and the "move" operation that is central to
nominal CatCrypt's state separation.

## Main definitions

* `Fresh` - Freshness relation (an atom is fresh for x if it's not in supp x)
* `Disj` - Disjointness of supports
* `move` - Generate a permutation that makes one element's support disjoint from another

## References

* [Pitts, *Nominal Sets*], Chapter 3
* [Benton et al., *Nominal SSProve*](https://eprint.iacr.org/2025/598)
-/

namespace CatCrypt.Nominal

/-- An atom is fresh for an element if it's not in the element's support. -/
def Fresh {α : Type*} [NomSet α] (a : Atom) (x : α) : Prop :=
  a ∉ NomSet.supp x

/-- Two elements are disjoint if their supports are disjoint. -/
def Disj {α β : Type*} [NomSet α] [NomSet β] (x : α) (y : β) : Prop :=
  Disjoint (NomSet.supp x) (NomSet.supp y)

namespace Fresh

variable {α : Type*} [NomSet α]

/-- Fresh atoms don't affect elements under permutation -/
theorem act_swap_fresh (a b : Atom) (x : α)
    (ha : Fresh a x) (hb : Fresh b x) :
    FinPerm.swap a b • x = x := by
  apply NomSet.act_eq_of_supp_fixed
  intro c hc
  apply FinPerm.swap_apply_of_ne_of_ne
  · intro heq; rw [heq] at hc; exact ha hc
  · intro heq; rw [heq] at hc; exact hb hc

end Fresh

/-- Generate a fresh atom not in the union of two supports -/
noncomputable def freshFor {α β : Type*} [NomSet α] [NomSet β] (x : α) (y : β) : Atom :=
  Atom.fresh (NomSet.supp x ∪ NomSet.supp y)

theorem freshFor_not_in_supp_left {α β : Type*} [NomSet α] [NomSet β] (x : α) (y : β) :
    Fresh (freshFor x y) x := by
  simp only [freshFor, Fresh]
  intro h
  apply Atom.fresh_not_mem
  exact Finset.mem_union_left _ h

theorem freshFor_not_in_supp_right {α β : Type*} [NomSet α] [NomSet β] (x : α) (y : β) :
    Fresh (freshFor x y) y := by
  simp only [freshFor, Fresh]
  intro h
  apply Atom.fresh_not_mem
  exact Finset.mem_union_right _ h

/-- The offset of a finset: one plus the maximum value.
    This is used to generate fresh atoms. -/
noncomputable def offset (s : Finset Atom) : ℕ := Atom.offset s

/-- Map an atom `a` to a fresh atom above the offset of some set.
    This is used to construct the fresh permutation. -/
def atomShift (base : ℕ) (a : Atom) : Atom := ⟨base + a.val⟩

theorem atomShift_injective (base : ℕ) : Function.Injective (atomShift base) := by
  intro a b h
  simp only [atomShift, Atom.mk.injEq] at h
  exact Atom.ext (Nat.add_left_cancel h)

theorem atomShift_image_disjoint {s : Finset Atom} {a : Atom} (ha : a ∈ s) (base : ℕ)
    (hbase : Atom.offset s ≤ base) : atomShift base a ∉ s := by
  intro hmem
  have hlt := Atom.fresh_val_gt hmem
  simp only [Atom.fresh, atomShift] at hlt
  omega

/-- Shifted atoms are above the offset -/
theorem atomShift_val_ge (base : ℕ) (a : Atom) : base ≤ (atomShift base a).val := by
  simp only [atomShift]
  omega

/-- Atoms in s are below the offset -/
theorem atom_val_lt_offset {s : Finset Atom} {a : Atom} (ha : a ∈ s) :
    a.val < Atom.offset s := Atom.fresh_val_gt ha

/-- Shifted atoms are not in the original set when base ≥ offset -/
theorem atomShift_not_in_set {s : Finset Atom} {a : Atom} (base : ℕ)
    (hbase : Atom.offset s ≤ base) : atomShift base a ∉ s := by
  intro h
  have hlt := atom_val_lt_offset h
  have hge := atomShift_val_ge base a
  omega

/-- Atoms in s have values strictly less than shifted atoms when base ≥ offset s -/
theorem atom_lt_shifted {s : Finset Atom} {base : ℕ} {a b : Atom}
    (hbase : Atom.offset s ≤ base) (ha : a ∈ s) : a.val < (atomShift base b).val := by
  have ha_lt := atom_val_lt_offset ha
  have hshift := atomShift_val_ge base b
  omega

/-- Shifted atoms are different from atoms in s -/
theorem shifted_ne_mem {s : Finset Atom} {base : ℕ} {a b : Atom}
    (hbase : Atom.offset s ≤ base) (hb : b ∈ s) : atomShift base a ≠ b := by
  intro heq
  have hlt := atom_lt_shifted hbase hb (a := b) (b := a)
  rw [heq] at hlt
  omega

/-- The fresh permutation construction.

    `freshPerm s base` creates a permutation that:
    - For each `a` in `s`, swaps `a` with `atomShift base a`
    - Acts as identity outside `s ∪ (atomShift base '' s)`

    The key property is that when `base ≥ offset s`, the images
    are above the offset, hence disjoint from any set with offset ≤ base.

    Following Rocq SSProve's `fperm (λ a, atomize (offset (supp x) + natize a)) (supp y)`. -/
noncomputable def freshPerm (s : Finset Atom) (base : ℕ) : FinPerm :=
  -- Build the permutation by composing swaps for each element
  -- We use List.foldl since FinPerm multiplication is associative
  s.toList.foldl (fun π a => π * FinPerm.swap a (atomShift base a)) 1

/-- Helper: if each swap in a fold fixes a point, the fold result fixes that point.
    This is a general induction principle for foldl with permutation multiplication. -/
theorem foldl_mul_swap_fix {a : Atom} {init : FinPerm} (l : List Atom) (base : ℕ)
    (hinit : init a = a)
    (hswaps : ∀ x ∈ l, a ≠ x ∧ a ≠ atomShift base x) :
    (l.foldl (fun π b => π * FinPerm.swap b (atomShift base b)) init) a = a := by
  induction l generalizing init with
  | nil => exact hinit
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have hx := hswaps x List.mem_cons_self
    have hxs : ∀ y ∈ xs, a ≠ y ∧ a ≠ atomShift base y :=
      fun y hy => hswaps y (List.mem_cons_of_mem x hy)
    -- The new init is init * swap x (atomShift base x)
    have hnew_init : (init * FinPerm.swap x (atomShift base x)) a = a := by
      simp only [FinPerm.mul_apply]
      rw [FinPerm.swap_apply_of_ne_of_ne hx.1 hx.2, hinit]
    exact ih hnew_init hxs

/-- freshPerm fixes atoms outside s when base ≥ offset s -/
theorem freshPerm_fix_outside {s : Finset Atom} {base : ℕ} {a : Atom}
    (hbase : Atom.offset s ≤ base) (ha : a ∉ s)
    (hshift : ∀ b ∈ s, atomShift base b ≠ a) :
    freshPerm s base a = a := by
  unfold freshPerm
  apply foldl_mul_swap_fix
  · rfl  -- init = 1 fixes a
  · intro x hx
    have hx_mem : x ∈ s := Finset.mem_toList.mp hx
    constructor
    · intro heq; exact ha (heq ▸ hx_mem)
    · intro heq; exact hshift x hx_mem heq.symm

/-- If all swaps in the list fix a point, the fold is transparent at that point:
    the fold result applied to x equals the initial permutation applied to x. -/
theorem foldl_mul_swap_transparent {x : Atom} {init : FinPerm} (l : List Atom) (base : ℕ)
    (hswaps : ∀ y ∈ l, x ≠ y ∧ x ≠ atomShift base y) :
    (l.foldl (fun π b => π * FinPerm.swap b (atomShift base b)) init) x = init x := by
  induction l generalizing init with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons]
    have hy := hswaps y List.mem_cons_self
    have hys : ∀ z ∈ ys, x ≠ z ∧ x ≠ atomShift base z :=
      fun z hz => hswaps z (List.mem_cons_of_mem y hz)
    -- (init * swap y (shift y)) x = init (swap y (shift y) x) = init x
    have hnew_init : (init * FinPerm.swap y (atomShift base y)) x = init x := by
      simp only [FinPerm.mul_apply]
      simp only [FinPerm.swap_apply_of_ne_of_ne hy.1 hy.2]
    rw [ih hys]
    exact hnew_init

/-- Helper for freshPerm_apply_mem': when a is in the list, the fold maps a to its shift.
    Key invariants: init fixes a, and init fixes atomShift base a. -/
theorem foldl_mul_swap_apply_mem {a : Atom} {init : FinPerm} (l : List Atom) (base : ℕ)
    (hnodup : l.Nodup)
    (ha : a ∈ l)
    (hinit : init a = a)
    (hinit_shift : init (atomShift base a) = atomShift base a)
    (hbefore : ∀ x ∈ l, x ≠ a → a.val < (atomShift base x).val)
    (hafter : ∀ x ∈ l, x ≠ a → (atomShift base a).val ≠ x.val ∧
                               atomShift base a ≠ atomShift base x) :
    (l.foldl (fun π b => π * FinPerm.swap b (atomShift base b)) init) a =
    atomShift base a := by
  induction l generalizing init with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp ha with
    | inl heq =>
      -- a = x, so this is the swap that moves a
      subst heq
      have hnodup' := List.nodup_cons.mp hnodup
      -- Key: all swaps in xs fix a (since a ∉ xs and shift of elements ≠ a)
      have hxs_fix_a : ∀ y ∈ xs, a ≠ y ∧ a ≠ atomShift base y := fun y hy => by
        have hy_ne : y ≠ a := fun h => hnodup'.1 (h ▸ hy)
        constructor
        · exact hy_ne.symm
        · intro heq'
          have hafter' := hafter y (List.mem_cons_of_mem a hy) hy_ne
          -- heq' : a = atomShift base y, but we need (atomShift base a).val ≠ y.val
          -- This should be impossible since a.val < base ≤ (atomShift base y).val
          -- So heq' should contradict something
          have h1 : a.val < (atomShift base y).val := by
            have h := hbefore y (List.mem_cons_of_mem a hy) hy_ne
            exact h
          rw [heq'] at h1
          exact absurd (le_refl _) (Nat.not_le.mpr h1)
      -- Use foldl_mul_swap_transparent: fold result at a equals (init * swap a (shift a)) a
      rw [foldl_mul_swap_transparent xs base hxs_fix_a]
      -- Now just compute (init * swap a (shift a)) a = init (shift a) = shift a
      simp only [FinPerm.mul_apply, FinPerm.swap_apply_left]
      exact hinit_shift

    | inr hxs =>
      -- a ≠ x, so swap x (atomShift base x) fixes a
      have ha_ne_x : a ≠ x := fun h => by
        have hnodup' := List.nodup_cons.mp hnodup
        exact hnodup'.1 (h ▸ hxs)
      have hbefore' := hbefore x List.mem_cons_self ha_ne_x.symm
      have ha_ne_shift : a ≠ atomShift base x := by
        intro heq; rw [heq] at hbefore'; omega
      have hnew : (init * FinPerm.swap x (atomShift base x)) a = a := by
        simp only [FinPerm.mul_apply]
        rw [FinPerm.swap_apply_of_ne_of_ne ha_ne_x ha_ne_shift, hinit]
      -- Also need to show (init * swap x (shift x)) fixes (shift a)
      have hafter_x := hafter x List.mem_cons_self ha_ne_x.symm
      have hnew_shift : (init * FinPerm.swap x (atomShift base x)) (atomShift base a) = atomShift base a := by
        simp only [FinPerm.mul_apply]
        have h1 : atomShift base a ≠ x := fun heq => hafter_x.1 (congrArg Atom.val heq)
        have h2 : atomShift base a ≠ atomShift base x := hafter_x.2
        rw [FinPerm.swap_apply_of_ne_of_ne h1 h2, hinit_shift]
      have hnodup' := (List.nodup_cons.mp hnodup).2
      exact ih hnodup' hxs hnew hnew_shift
        (fun y hy hy_ne => hbefore y (List.mem_cons_of_mem x hy) hy_ne)
        (fun y hy hy_ne => hafter y (List.mem_cons_of_mem x hy) hy_ne)

/-- freshPerm maps atoms in s to their shifts when base ≥ offset -/
theorem freshPerm_apply_mem' {s : Finset Atom} {base : ℕ} {a : Atom}
    (hbase : Atom.offset s ≤ base) (ha : a ∈ s) :
    freshPerm s base a = atomShift base a := by
  unfold freshPerm
  apply foldl_mul_swap_apply_mem s.toList base s.nodup_toList
  · exact Finset.mem_toList.mpr ha
  · rfl  -- init = 1 fixes a
  · rfl  -- init = 1 fixes atomShift base a
  · intro x _ _
    exact atom_lt_shifted hbase ha
  · intro x hx hx_ne
    have hx_mem := Finset.mem_toList.mp hx
    constructor
    · intro heq
      have h1 := atom_lt_shifted hbase hx_mem (a := x) (b := a)
      omega
    · intro heq
      have := atomShift_injective base heq
      exact hx_ne this.symm

/-- Support of an element under freshPerm shifts appropriately.
    The support of π ∙ y is π '' (supp y), so it consists of shifted atoms
    which have values ≥ base, while atoms in sups have values < offset sups ≤ base. -/
theorem supp_act_freshPerm_disjoint {α : Type*} [NomSet α] (y : α) (base : ℕ)
    (hbase : Atom.offset (NomSet.supp y) ≤ base)
    (sups : Finset Atom) (hsups : Atom.offset sups ≤ base) :
    Disjoint sups (NomSet.supp (freshPerm (NomSet.supp y) base • y)) := by
  -- Use the support equivariance: supp (π ∙ y) = π '' (supp y)
  rw [NomSet.supp_act_eq_image]
  -- Now show sups and (supp y).image (freshPerm ...) are disjoint
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb hab
  subst hab
  -- a ∈ sups, so a.val < offset sups ≤ base
  have ha_lt : a.val < base := by
    have h := atom_val_lt_offset ha
    omega
  -- b ∈ (supp y).image (freshPerm ...), so b = freshPerm c for some c ∈ supp y
  rw [Finset.mem_image] at hb
  obtain ⟨c, hc, hca⟩ := hb
  -- freshPerm maps c ∈ supp y to atomShift base c
  rw [freshPerm_apply_mem' hbase hc] at hca
  -- So a = atomShift base c with a.val = base + c.val ≥ base
  have ha_ge : a.val ≥ base := by
    rw [← hca]
    exact atomShift_val_ge base c
  -- Contradiction: a.val < base and a.val ≥ base
  omega

/-- The fresh permutation for move: maps supp y to atoms above offset(supp x ∪ supp y) -/
noncomputable def freshMove {α β : Type*} [NomSet α] [NomSet β] (x : α) (y : β) : FinPerm :=
  let combined := NomSet.supp x ∪ NomSet.supp y
  freshPerm (NomSet.supp y) (Atom.offset combined)

/-- The move permutation: applies freshMove to relocate y's support away from x's support.

    This follows the Rocq definition: `move x y := fresh x y ∙ y`
    where `fresh x y` is the permutation mapping `supp y` to fresh atoms. -/
noncomputable def move {α β : Type*} [NomSet α] [NomSet β] (x : α) (y : β) : β :=
  freshMove x y • y

/-- The permutation used by move -/
noncomputable def movePerm {α β : Type*} [NomSet α] [NomSet β] (x : α) (y : β) : FinPerm :=
  freshMove x y

/-- After applying move, the supports become disjoint.

    This is the key property from nominal set theory (Rocq: `fresh_disjoint`).

    **Proof sketch:**
    - `freshMove x y` maps atoms in `supp y` to atoms above `offset(supp x ∪ supp y)`
    - All atoms in `supp x` are below this offset
    - Therefore, `supp(move x y) ∩ supp x = ∅`

    Note: The current implementation has sorries in the helper lemmas that
    require careful handling of the fold construction. These are provable
    using standard techniques but require significant technical machinery. -/
theorem move_disj {α β : Type*} [NomSet α] [NomSet β] (x : α) (y : β) :
    Disj x (move x y) := by
  unfold Disj move freshMove
  -- supp x is disjoint from supp(freshPerm (supp y) (offset(supp x ∪ supp y)) ∙ y)
  -- because:
  -- 1. All atoms in supp(freshPerm ... ∙ y) are ≥ offset(supp x ∪ supp y)
  -- 2. All atoms in supp x are < offset(supp x ∪ supp y)
  have hoff : Atom.offset (NomSet.supp x) ≤ Atom.offset (NomSet.supp x ∪ NomSet.supp y) := by
    simp only [Atom.offset]
    split_ifs with h1 h2 h2
    · -- Both nonempty: x nonempty and union nonempty
      have hsub : NomSet.supp x ⊆ NomSet.supp x ∪ NomSet.supp y := Finset.subset_union_left
      -- For any a in supp x, a.val ≤ sup' (supp x) ≤ sup' (supp x ∪ supp y)
      have hunion : h1.choose ∈ NomSet.supp x ∪ NomSet.supp y :=
        hsub h1.choose_spec
      have hle_x : (NomSet.supp x).sup' h1 Atom.val ≤ (NomSet.supp x ∪ NomSet.supp y).sup' h2 Atom.val := by
        apply Finset.sup'_le h1
        intro a ha
        exact Finset.le_sup' _ (hsub ha)
      omega
    · -- x nonempty, union empty - contradiction
      simp only [Finset.not_nonempty_iff_eq_empty, Finset.union_eq_empty] at h2
      simp only [h2.1, Finset.not_nonempty_empty] at h1
    · omega
    · omega
  apply supp_act_freshPerm_disjoint
  · simp only [Atom.offset]
    split_ifs with h1 h2 h2
    · have hsub : NomSet.supp y ⊆ NomSet.supp x ∪ NomSet.supp y := Finset.subset_union_right
      have hle_y : (NomSet.supp y).sup' h1 Atom.val ≤ (NomSet.supp x ∪ NomSet.supp y).sup' h2 Atom.val := by
        apply Finset.sup'_le h1
        intro a ha
        exact Finset.le_sup' _ (hsub ha)
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty, Finset.union_eq_empty] at h2
      simp only [h2.2, Finset.not_nonempty_empty] at h1
    · omega
    · omega
  · exact hoff

/-- movePerm doesn't move the first argument when supports are disjoint.

    Note: This requires the disjointness hypothesis because freshPerm moves
    all atoms in supp y. If a ∈ supp x ∩ supp y, then a would be moved. -/
theorem movePerm_act_left {α β : Type*} [NomSet α] [NomSet β] (x : α) (y : β)
    (hdisj : Disjoint (NomSet.supp x) (NomSet.supp y)) :
    movePerm x y • x = x := by
  -- The permutation only moves atoms in supp y to fresh atoms
  -- Since supp x and supp y are disjoint, atoms in supp x are not moved
  apply NomSet.act_eq_of_supp_fixed
  intro a ha
  -- a ∈ supp x, and since supp x ∩ supp y = ∅, a ∉ supp y
  have ha_not_y : a ∉ NomSet.supp y := Finset.disjoint_left.mp hdisj ha
  -- movePerm x y = freshPerm (supp y) (offset (supp x ∪ supp y))
  unfold movePerm freshMove
  -- freshPerm fixes atoms outside supp y (and not in the shift image)
  apply freshPerm_fix_outside
  · -- offset (supp y) ≤ offset (supp x ∪ supp y)
    simp only [Atom.offset]
    split_ifs with h1 h2 h2
    · have hsub : NomSet.supp y ⊆ NomSet.supp x ∪ NomSet.supp y := Finset.subset_union_right
      have hle : (NomSet.supp y).sup' h1 Atom.val ≤ (NomSet.supp x ∪ NomSet.supp y).sup' h2 Atom.val := by
        apply Finset.sup'_le h1
        intro b hb
        exact Finset.le_sup' _ (hsub hb)
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty, Finset.union_eq_empty] at h2
      simp only [h2.2, Finset.not_nonempty_empty] at h1
    · omega
    · omega
  · exact ha_not_y
  · -- a is not a shift target: ∀ b ∈ supp y, atomShift base b ≠ a
    intro b hb
    -- atomShift base b has value ≥ base = offset (supp x ∪ supp y)
    -- a ∈ supp x has value < offset (supp x ∪ supp y)
    intro heq
    have ha_mem : a ∈ NomSet.supp x ∪ NomSet.supp y := Finset.mem_union_left _ ha
    have ha_lt : a.val < Atom.offset (NomSet.supp x ∪ NomSet.supp y) := atom_val_lt_offset ha_mem
    have hshift_ge : (atomShift (Atom.offset (NomSet.supp x ∪ NomSet.supp y)) b).val ≥
                     Atom.offset (NomSet.supp x ∪ NomSet.supp y) :=
      atomShift_val_ge _ b
    -- heq : atomShift ... b = a, so a.val = (atomShift ...).val ≥ offset
    have heq_val : a.val = (atomShift (Atom.offset (NomSet.supp x ∪ NomSet.supp y)) b).val :=
      congrArg Atom.val heq.symm
    omega

/-- Alpha-equivalence: two elements are equivalent if they differ only by a permutation -/
def AlphaEquiv {α : Type*} [NomSet α] (x y : α) : Prop :=
  ∃ π : FinPerm, π • x = y

notation:50 x " ≡α " y => AlphaEquiv x y

namespace AlphaEquiv

variable {α : Type*} [NomSet α]

theorem refl (x : α) : x ≡α x := ⟨1, one_smul FinPerm x⟩

theorem symm {x y : α} (h : x ≡α y) : y ≡α x := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨π⁻¹, by rw [← hπ, inv_smul_smul]⟩

theorem trans {x y z : α} (hxy : x ≡α y) (hyz : y ≡α z) : x ≡α z := by
  obtain ⟨π₁, hπ₁⟩ := hxy
  obtain ⟨π₂, hπ₂⟩ := hyz
  exact ⟨π₂ * π₁, by rw [mul_smul, hπ₁, hπ₂]⟩

end AlphaEquiv

end CatCrypt.Nominal
