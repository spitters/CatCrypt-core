/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Prob.SDistr

/-!
# Couplings

This file defines couplings of sub-distributions and the lifting operation
that is fundamental to probabilistic relational Hoare logic.

## Main definitions

* `Coupling d₁ d₂` - A coupling of two sub-distributions
* `Coupling.satisfies` - A coupling satisfies a relation
* `liftR R d₁ d₂` - Relation R lifts to distributions (there exists a coupling satisfying R)

## Main results

* `liftR_refl` - Equality lifts to any distribution (diagonal coupling)
* `liftR_mono` - Lifting is monotone in the relation
* `liftR_bind` - Lifting composes through bind (key for bind rule)

## References

* Probabilistic couplings in verification
* CatCrypt: theories/Crypt/rhl_semantics/only_prob/Couplings.v
-/

namespace CatCrypt.Prob

open PMF

variable {α β γ δ : Type*}

/-! ## Coupling definition -/

/-- A coupling of two sub-distributions.
    The joint distribution has the correct marginals. -/
structure Coupling (d₁ : SDistr α) (d₂ : SDistr β) where
  /-- The joint distribution -/
  joint : SDistr (α × β)
  /-- Left marginal condition: projecting gives d₁ -/
  left_marginal : ∀ a, (joint.bind fun p => SDistr.pure p.1) (some a) = d₁ (some a)
  /-- Right marginal condition: projecting gives d₂ -/
  right_marginal : ∀ b, (joint.bind fun p => SDistr.pure p.2) (some b) = d₂ (some b)

namespace Coupling

variable {d₁ : SDistr α} {d₂ : SDistr β}

/-- A coupling satisfies relation R if all coupled pairs satisfy R -/
def satisfies (c : Coupling d₁ d₂) (R : α → β → Prop) : Prop :=
  ∀ a b, c.joint (some (a, b)) ≠ 0 → R a b

/-- If (a, b) has nonzero joint mass, then a has nonzero left marginal mass.

    Proof: By the left marginal condition,
    `d₁ (some a) = ∑' b', joint (some (a, b'))` (modulo encoding).
    Since `joint (some (a, b)) ≠ 0`, the sum is nonzero. -/
theorem in_left_support (c : Coupling d₁ d₂) {a : α} {b : β}
    (h : c.joint (some (a, b)) ≠ 0) : d₁ (some a) ≠ 0 := by
  rw [← c.left_marginal a]
  simp only [SDistr.bind, PMF.bind_apply]
  intro hzero
  apply h
  rw [ENNReal.tsum_eq_zero] at hzero
  have := hzero (some (a, b))
  simp only [SDistr.pure, PMF.pure_apply] at this
  simp only [ite_true, mul_one] at this
  exact this

/-- If (a, b) has nonzero joint mass, then b has nonzero right marginal mass. -/
theorem in_right_support (c : Coupling d₁ d₂) {a : α} {b : β}
    (h : c.joint (some (a, b)) ≠ 0) : d₂ (some b) ≠ 0 := by
  rw [← c.right_marginal b]
  simp only [SDistr.bind, PMF.bind_apply]
  intro hzero
  apply h
  rw [ENNReal.tsum_eq_zero] at hzero
  have := hzero (some (a, b))
  simp only [SDistr.pure, PMF.pure_apply] at this
  simp only [ite_true, mul_one] at this
  exact this

end Coupling

/-! ## Lifting relation to distributions -/

/-- Lifting: relation R lifts from values to distributions if there exists
    a coupling where all coupled pairs satisfy R. -/
def liftR (R : α → β → Prop) (d₁ : SDistr α) (d₂ : SDistr β) : Prop :=
  ∃ c : Coupling d₁ d₂, c.satisfies R

/-- Notation for lifting -/
notation:50 d₁ " ⟨" R "⟩# " d₂ => liftR R d₁ d₂

/-! ## Standard coupling constructions -/

/-- Diagonal/identity coupling: couple each element with itself -/
noncomputable def Coupling.diagonal (d : SDistr α) : Coupling d d where
  joint := d.bind fun a => SDistr.pure (a, a)
  left_marginal := fun a => by
    -- Need: (d.bind (fun a => pure (a,a))).bind (fun p => pure p.1) (some a) = d (some a)
    -- By bind associativity and pure_bind:
    -- = d.bind (fun x => (pure (x,x)).bind (fun p => pure p.1)) (some a)
    -- = d.bind (fun x => pure x) (some a)
    -- = d (some a)
    rw [SDistr.bind_assoc]
    -- Now: (d.bind fun x => (SDistr.pure (x, x)).bind fun p => SDistr.pure p.1) (some a)
    have h : (fun (x : α) => (SDistr.pure (x, x)).bind fun p => SDistr.pure p.1) =
             fun (x : α) => SDistr.pure x := by
      funext x; rw [SDistr.pure_bind]
    rw [h, SDistr.bind_pure]
  right_marginal := fun a => by
    rw [SDistr.bind_assoc]
    have h : (fun (x : α) => (SDistr.pure (x, x)).bind fun p => SDistr.pure p.2) =
             fun (x : α) => SDistr.pure x := by
      funext x; rw [SDistr.pure_bind]
    rw [h, SDistr.bind_pure]

/-- Bijection coupling: couple a with f(a) -/
noncomputable def Coupling.fromBij (d : SDistr α) (f : α ≃ β) :
    Coupling d (d.bind fun a => SDistr.pure (f a)) where
  joint := d.bind fun a => SDistr.pure (a, f a)
  left_marginal := fun a => by
    rw [SDistr.bind_assoc]
    have h : (fun (x : α) => (SDistr.pure (x, f x)).bind fun p => SDistr.pure p.1) =
             fun (x : α) => SDistr.pure x := by
      funext x; rw [SDistr.pure_bind]
    rw [h, SDistr.bind_pure]
  right_marginal := fun b => by
    rw [SDistr.bind_assoc]
    have h : (fun (x : α) => (SDistr.pure (x, f x)).bind fun p => SDistr.pure p.2) =
             fun (x : α) => SDistr.pure (f x) := by
      funext x; rw [SDistr.pure_bind]
    rw [h]

/-! ## Key lifting lemmas -/

/-- Reflexivity: equality always lifts (via diagonal coupling) -/
theorem liftR_refl (d : SDistr α) : d ⟨Eq⟩# d := by
  use Coupling.diagonal d
  intro a b hab
  -- In diagonal coupling, joint = d.bind (fun x => pure (x, x))
  -- joint (some (a, b)) ≠ 0 means a = b
  simp only [Coupling.diagonal, SDistr.bind, PMF.bind_apply] at hab
  by_contra hne
  -- If a ≠ b, the sum is 0, contradicting hab
  apply hab
  rw [ENNReal.tsum_eq_zero]
  intro oa
  cases oa with
  | none => simp [SDistr.fail, PMF.pure_apply]
  | some x =>
    simp only [SDistr.pure, PMF.pure_apply]
    -- The term is: d (some x) * (if some (a, b) = some (x, x) then 1 else 0)
    -- some (a, b) = some (x, x) iff (a, b) = (x, x) iff a = x ∧ b = x
    -- Since a ≠ b, we can't have a = x ∧ b = x
    have hneq : ¬(some (a, b) = some (x, x)) := by
      simp only [Option.some.injEq, Prod.mk.injEq]
      intro ⟨ha, hb⟩
      exact hne (ha.trans hb.symm)
    rw [if_neg hneq, mul_zero]

/-- Monotonicity: if R ⊆ S and R lifts, then S lifts -/
theorem liftR_mono {R S : α → β → Prop} {d₁ : SDistr α} {d₂ : SDistr β}
    (hRS : ∀ a b, R a b → S a b) (h : d₁ ⟨R⟩# d₂) : d₁ ⟨S⟩# d₂ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun a b hab => hRS a b (hc a b hab)⟩

/-- Symmetry: if R lifts, then R⁻¹ lifts with swapped distributions -/
theorem liftR_symm {R : α → β → Prop} {d₁ : SDistr α} {d₂ : SDistr β}
    (h : d₁ ⟨R⟩# d₂) : d₂ ⟨fun b a => R a b⟩# d₁ := by
  obtain ⟨c, hc⟩ := h
  -- Construct swapped coupling
  use {
    joint := c.joint.bind fun p => SDistr.pure (p.2, p.1)
    left_marginal := fun b => by
      rw [SDistr.bind_assoc]
      -- Inner function: (α × β) → SDistr β
      have h2 : (fun (p : α × β) => (SDistr.pure (p.2, p.1) : SDistr (β × α)).bind
                  fun (q : β × α) => SDistr.pure q.1) =
                (fun (p : α × β) => SDistr.pure p.2) := by
        funext p; rw [SDistr.pure_bind]
      rw [h2]
      exact c.right_marginal b
    right_marginal := fun a => by
      rw [SDistr.bind_assoc]
      have h2 : (fun (p : α × β) => (SDistr.pure (p.2, p.1) : SDistr (β × α)).bind
                  fun (q : β × α) => SDistr.pure q.2) =
                (fun (p : α × β) => SDistr.pure p.1) := by
        funext p; rw [SDistr.pure_bind]
      rw [h2]
      exact c.left_marginal a
  }
  intro b a hab
  -- hab : swapped_joint (some (b, a)) ≠ 0
  -- Need to show R a b
  simp only [SDistr.bind, PMF.bind_apply] at hab
  -- The sum is nonzero, so some term is nonzero
  by_contra hRab
  apply hab
  rw [ENNReal.tsum_eq_zero]
  intro op
  cases op with
  | none => simp [SDistr.fail, PMF.pure_apply]
  | some p =>
    simp only [SDistr.pure, PMF.pure_apply]
    -- Term is: c.joint (some p) * (if some (b, a) = some (p.2, p.1) then 1 else 0)
    -- If the condition holds, p.2 = b and p.1 = a, so p = (a, b)
    -- Then c.joint (some (a, b)) ≠ 0 would give R a b via hc, contradicting hRab
    by_cases heq : some (b, a) = some (p.2, p.1)
    · simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨hb, ha⟩ := heq
      -- p = (a, b)
      have hp : p = (a, b) := Prod.ext ha.symm hb.symm
      rw [hp]
      -- Now the if condition is true for (a, b)
      have hcond : some (b, a) = some ((a, b).2, (a, b).1) := rfl
      simp only [hcond, ↓reduceIte]
      -- If c.joint (some (a, b)) ≠ 0, then hc gives R a b, contradiction
      by_cases hjoint : c.joint (some (a, b)) = 0
      · simp [hjoint]
      · exfalso; exact hRab (hc a b hjoint)
    · simp only [heq, ↓reduceIte, mul_zero]

/-! ## Marginal sum lemmas -/

/-- If mass d = 1, then d none = 0 -/
private theorem SDistr.mass_one_implies_none_zero {d : SDistr α} (h : SDistr.mass d = 1) :
    d none = 0 := by
  unfold SDistr.mass at h
  -- h : 1 - d none = 1
  -- In ENNReal: 1 - x = 1 implies x = 0 (when x ≤ 1)
  -- From 1 - d none = 1, we get d none = 0
  by_contra hne
  -- If d none ≠ 0, then 1 - d none < 1
  have h1 : (1 : ENNReal) - d none < 1 := by
    apply ENNReal.sub_lt_self
    · norm_num  -- 1 ≠ ⊤
    · norm_num  -- 1 ≠ 0
    · exact hne
  exact absurd h (ne_of_lt h1)

/-- Binding with a constant (when mass = 1) -/
private theorem SDistr.bind_const_mass_one {d : SDistr α} {e : SDistr β}
    (h : SDistr.mass d = 1) : d.bind (fun _ => e) = e := by
  have hd_none := SDistr.mass_one_implies_none_zero h
  -- d.bind (fun _ => e) = e when d is a proper distribution (d none = 0)
  apply SDistr.eq_of_some_eq
  intro b
  simp only [SDistr.bind, PMF.bind_apply]
  -- Goal: ∑' a, d a * (match a with some _ => e | none => fail) (some b) = e (some b)
  -- Split the sum: none term + some terms
  rw [SDistr.tsum_option_eq_add]
  -- none term: d none * fail (some b) = 0 * 0 = 0
  simp only [SDistr.fail_apply_some, mul_zero, zero_add]
  -- some terms: ∑' a, d (some a) * e (some b) = e (some b)
  -- Use commutativity then factor out e (some b) using tsum_mul_left
  have hsum_eq : ∑' a : α, d (some a) * e (some b) = ∑' a : α, e (some b) * d (some a) := by
    apply tsum_congr; intro a; ring
  rw [hsum_eq, ENNReal.tsum_mul_left]
  -- Need ∑' a, d (some a) = 1
  have hsum : ∑' a : α, d (some a) = 1 := by
    have htotal := PMF.tsum_coe d
    rw [SDistr.tsum_option_eq_add] at htotal
    rw [hd_none, zero_add] at htotal
    exact htotal
  rw [hsum, mul_one]

/-- Product coupling: independent sampling.
    Requires both distributions to have mass 1 (i.e., no failure probability).
    For sub-distributions with mass < 1, the product joint has marginals
    that are scaled by the other distribution's mass.

    Note: This coupling is not used in the main pRHL development, which uses
    `liftR_bind` for composition instead. -/
noncomputable def Coupling.prod (d₁ : SDistr α) (d₂ : SDistr β)
    (h₁ : SDistr.mass d₁ = 1) (h₂ : SDistr.mass d₂ = 1) : Coupling d₁ d₂ where
  joint := d₁.bind fun a => d₂.bind fun b => SDistr.pure (a, b)
  left_marginal := fun a₀ => by
    -- Goal: (d₁.bind (fun a => d₂.bind (fun b => pure (a, b)))).bind proj1 (some a₀) = d₁ (some a₀)
    rw [SDistr.bind_assoc]
    -- Now: d₁.bind (fun a => (d₂.bind (fun b => pure (a, b))).bind proj1) (some a₀)
    have h_inner : ∀ (a : α), (d₂.bind (fun b => SDistr.pure (a, b))).bind
                        (fun p => SDistr.pure p.1) = SDistr.pure a := by
      intro a
      rw [SDistr.bind_assoc]
      have h_pure : (fun (b : β) => (SDistr.pure (a, b)).bind (fun p => SDistr.pure p.1))
                  = (fun (_ : β) => SDistr.pure a) := by
        funext b; rw [SDistr.pure_bind]
      rw [h_pure, SDistr.bind_const_mass_one h₂]
    simp only [h_inner, SDistr.bind_pure]
  right_marginal := fun b₀ => by
    rw [SDistr.bind_assoc]
    have h_inner : ∀ (a : α), (d₂.bind (fun b => SDistr.pure (a, b))).bind
                        (fun p => SDistr.pure p.2) = d₂ := by
      intro a
      rw [SDistr.bind_assoc]
      have h_pure : (fun (b : β) => (SDistr.pure (a, b)).bind (fun p => SDistr.pure p.2))
                  = (fun (b : β) => SDistr.pure b) := by
        funext b; rw [SDistr.pure_bind]
      rw [h_pure, SDistr.bind_pure]
    simp only [h_inner]
    -- Now: d₁.bind (fun _ => d₂) = d₂ (by mass condition)
    rw [SDistr.bind_const_mass_one h₁]

/-- The left marginal condition implies a sum identity:
    ∑' b, joint (some (a, b)) = d₁ (some a) -/
theorem Coupling.left_marginal_sum {d₁ : SDistr α} {d₂ : SDistr β}
    (c : Coupling d₁ d₂) (a₀ : α) :
    ∑' b, c.joint (some (a₀, b)) = d₁ (some a₀) := by
  classical
  have hlm := c.left_marginal a₀
  simp only [SDistr.bind, PMF.bind_apply, SDistr.pure, SDistr.fail] at hlm

  -- Define projection and the function appearing in hlm
  let proj : Option (α × β) → SDistr α := fun x => match x with | some p => PMF.pure (some p.1) | none => PMF.pure none
  let f : Option (α × β) → ENNReal := fun x => c.joint x * proj x (some a₀)

  -- f none = 0
  have hf_none : f none = 0 := by simp [f, proj, PMF.pure_apply]

  -- f (some p) simplifies to indicator
  have hf_some : ∀ p, f (some p) = c.joint (some p) * (if p.1 = a₀ then 1 else 0) := by
    intro p
    simp only [f, proj, PMF.pure_apply, Option.some.injEq]
    congr 1
    simp only [eq_comm]

  -- hlm uses the same function
  have hlm_f : ∑' x, f x = d₁ (some a₀) := by
    convert hlm using 2
    funext x; cases x <;> rfl

  -- Split sum over Option to sum over some
  have h_split : ∑' x, f x = ∑' p, f (some p) := SDistr.tsum_option_none_zero f hf_none

  -- Simplify using indicator form
  have h_simp : ∑' p, f (some p) = ∑' p : α × β, c.joint (some p) * (if p.1 = a₀ then 1 else 0) := by
    apply tsum_congr; intro p; exact hf_some p

  -- Collapse the indicator via product tsum
  have h_indicator : ∑' p : α × β, c.joint (some p) * (if p.1 = a₀ then 1 else 0)
                   = ∑' b, c.joint (some (a₀, b)) := by
    rw [ENNReal.tsum_prod', tsum_eq_single a₀]
    · simp only [↓reduceIte, mul_one]
    · intro a ha; simp only [ha, ↓reduceIte, mul_zero, tsum_zero]

  -- Chain the equalities
  calc ∑' b, c.joint (some (a₀, b))
      = ∑' p : α × β, c.joint (some p) * (if p.1 = a₀ then 1 else 0) := h_indicator.symm
    _ = ∑' p, f (some p) := h_simp.symm
    _ = ∑' x, f x := h_split.symm
    _ = d₁ (some a₀) := hlm_f

/-- The right marginal condition implies a sum identity:
    ∑' a, joint (some (a, b)) = d₂ (some b) -/
theorem Coupling.right_marginal_sum {d₁ : SDistr α} {d₂ : SDistr β}
    (c : Coupling d₁ d₂) (b₀ : β) :
    ∑' a, c.joint (some (a, b₀)) = d₂ (some b₀) := by
  classical
  have hrm := c.right_marginal b₀
  simp only [SDistr.bind, PMF.bind_apply, SDistr.pure, SDistr.fail] at hrm

  -- Define projection and the function appearing in hrm
  let proj : Option (α × β) → SDistr β := fun x => match x with | some p => PMF.pure (some p.2) | none => PMF.pure none
  let f : Option (α × β) → ENNReal := fun x => c.joint x * proj x (some b₀)

  -- f none = 0
  have hf_none : f none = 0 := by simp [f, proj, PMF.pure_apply]

  -- f (some p) simplifies to indicator
  have hf_some : ∀ p, f (some p) = c.joint (some p) * (if p.2 = b₀ then 1 else 0) := by
    intro p
    simp only [f, proj, PMF.pure_apply, Option.some.injEq]
    congr 1
    simp only [eq_comm]

  -- hrm uses the same function
  have hrm_f : ∑' x, f x = d₂ (some b₀) := by
    convert hrm using 2
    funext x; cases x <;> rfl

  -- Split sum over Option to sum over some
  have h_split : ∑' x, f x = ∑' p, f (some p) := SDistr.tsum_option_none_zero f hf_none

  -- Simplify using indicator form
  have h_simp : ∑' p, f (some p) = ∑' p : α × β, c.joint (some p) * (if p.2 = b₀ then 1 else 0) := by
    apply tsum_congr; intro p; exact hf_some p

  -- Collapse the indicator via product tsum
  have h_indicator : ∑' p : α × β, c.joint (some p) * (if p.2 = b₀ then 1 else 0)
                   = ∑' a, c.joint (some (a, b₀)) := by
    rw [ENNReal.tsum_prod']
    apply tsum_congr
    intro a
    rw [tsum_eq_single b₀]
    · simp only [↓reduceIte, mul_one]
    · intro b hb; simp only [hb, ↓reduceIte, mul_zero]

  -- Chain the equalities
  calc ∑' a, c.joint (some (a, b₀))
      = ∑' p : α × β, c.joint (some p) * (if p.2 = b₀ then 1 else 0) := h_indicator.symm
    _ = ∑' p, f (some p) := h_simp.symm
    _ = ∑' x, f x := h_split.symm
    _ = d₂ (some b₀) := hrm_f

/-- If d₁ and d₂ are coupled by equality (diagonal coupling only),
    then they are equal as distributions.
    Key insight: equality coupling forces all mass to be on the diagonal,
    and marginal sums on the diagonal give the same values for both. -/
theorem liftR_eq_implies_eq {d₁ d₂ : SDistr α}
    (h : d₁ ⟨Eq⟩# d₂) : d₁ = d₂ := by
  obtain ⟨c, hc⟩ := h
  -- hc: for all (a, b) with c.joint (some (a, b)) ≠ 0, a = b
  -- This means c.joint only has mass on the diagonal.
  -- For off-diagonal pairs, c.joint (some (a, b)) = 0.
  have h_off_diag : ∀ a b, a ≠ b → c.joint (some (a, b)) = 0 := by
    intro a b hne
    by_contra hnonzero
    exact hne (hc a b hnonzero)
  -- The marginal sums use indicator logic. Since only diagonal terms are nonzero:
  -- d₁ (some a) = ∑_b c.joint (some (a, b)) = c.joint (some (a, a))
  -- d₂ (some a) = ∑_a' c.joint (some (a', a)) = c.joint (some (a, a))
  apply SDistr.eq_of_some_eq
  intro a
  have hlm := c.left_marginal_sum a
  have hrm := c.right_marginal_sum a
  -- hlm: ∑' b, c.joint (some (a, b)) = d₁ (some a)
  -- hrm: ∑' a', c.joint (some (a', a)) = d₂ (some a)
  -- Both sums collapse to c.joint (some (a, a))
  have hlm_diag : ∑' b, c.joint (some (a, b)) = c.joint (some (a, a)) := by
    rw [tsum_eq_single a]
    intro b hne
    exact h_off_diag a b (Ne.symm hne)
  have hrm_diag : ∑' a', c.joint (some (a', a)) = c.joint (some (a, a)) := by
    rw [tsum_eq_single a]
    intro a' hne
    exact h_off_diag a' a hne
  rw [hlm_diag] at hlm
  rw [hrm_diag] at hrm
  rw [← hlm, ← hrm]

/-- Transitivity for equality -/
theorem liftR_trans_eq {d₁ d₂ d₃ : SDistr α}
    (h₁₂ : d₁ ⟨Eq⟩# d₂) (h₂₃ : d₂ ⟨Eq⟩# d₃) : d₁ ⟨Eq⟩# d₃ := by
  -- From equality couplings, we get d₁ = d₂ = d₃
  have heq₁₂ := liftR_eq_implies_eq h₁₂
  have heq₂₃ := liftR_eq_implies_eq h₂₃
  rw [heq₁₂, heq₂₃]
  exact liftR_refl d₃

/-- Helper: given a joint distribution, continuation coupling `kd`, and a marginal condition,
    prove that projecting the composed joint gives the expected bound distribution.
    This abstracts the shared proof structure used for both left and right marginals
    in `liftR_bind`. -/
private theorem coupling_marginal_proof
    {α' β' γ' δ' ε₁ ε₂ : Type*}
    (joint : SDistr (α' × β'))
    (kd : α' × β' → SDistr (γ' × δ'))
    (proj : γ' × δ' → ε₁) (sel : α' × β' → ε₂)
    (fi : ε₂ → SDistr ε₁) (di : SDistr ε₂)
    (inner : ∀ a b, joint (some (a, b)) ≠ 0 →
      (kd (a, b)).bind (fun p' => SDistr.pure (proj p')) = fi (sel (a, b)))
    (marginal : ∀ x, (joint.bind (fun p => SDistr.pure (sel p))) (some x) = di (some x))
    (x : ε₁) :
    ((joint.bind kd).bind (fun p' => SDistr.pure (proj p'))) (some x) = (di.bind fi) (some x) := by
  rw [SDistr.bind_assoc]
  have h_bind_eq : joint.bind (fun p => (kd p).bind (fun p' => SDistr.pure (proj p')))
                 = joint.bind (fun p => fi (sel p)) := by
    apply SDistr.bind_congr_support
    intro p hop
    exact inner p.1 p.2 hop
  rw [h_bind_eq]
  have h_to_marginal : joint.bind (fun p => fi (sel p))
                     = (joint.bind (fun p => SDistr.pure (sel p))).bind fi := by
    symm
    rw [SDistr.bind_assoc]
    apply SDistr.bind_congr_support
    intro p _
    rw [SDistr.pure_bind]
  rw [h_to_marginal]
  have h_marginal : joint.bind (fun p => SDistr.pure (sel p)) = di :=
    SDistr.eq_of_some_eq marginal
  rw [h_marginal]

/-- Composition through bind (THE KEY LEMMA for pRHL)
    This is the fundamental lemma that makes probabilistic relational Hoare logic work.
    The construction composes couplings:
    1. Sample (a, b) from the coupling of d₁ and d₂
    2. For each sampled pair, use the coupling from hf to get the continuation coupling
    3. The result is a coupling of the bound computations

    The key challenge in the formal proof is that `hf` requires `R a b`, but we only
    know `R a b` when `c.joint (some (a, b)) ≠ 0`. We use Classical.choice to pick
    couplings for pairs outside the support (any choice works since they have zero measure). -/
theorem liftR_bind {d₁ : SDistr α} {d₂ : SDistr β}
    {f₁ : α → SDistr γ} {f₂ : β → SDistr δ}
    {R : α → β → Prop} {S : γ → δ → Prop}
    (hd : d₁ ⟨R⟩# d₂)
    (hf : ∀ a b, R a b → (f₁ a) ⟨S⟩# (f₂ b)) :
    (d₁.bind f₁) ⟨S⟩# (d₂.bind f₂) := by
  classical
  obtain ⟨c, hc⟩ := hd
  let kd : α × β → SDistr (γ × δ) := fun ⟨a, b⟩ =>
    if h : c.joint (some (a, b)) ≠ 0 then
      (hf a b (hc a b h)).choose.joint
    else
      (f₁ a).bind fun c => (f₂ b).bind fun d => SDistr.pure (c, d)
  let joint_composed : SDistr (γ × δ) := c.joint.bind kd
  use {
    joint := joint_composed
    left_marginal := fun g => by
      simp only [joint_composed]
      exact coupling_marginal_proof c.joint kd Prod.fst Prod.fst f₁ d₁
        (fun a b hne => by
          simp only [kd, dif_pos hne]
          apply SDistr.eq_of_some_eq
          exact (hf a b (hc a b hne)).choose.left_marginal)
        c.left_marginal g
    right_marginal := fun d => by
      simp only [joint_composed]
      exact coupling_marginal_proof c.joint kd Prod.snd Prod.snd f₂ d₂
        (fun a b hne => by
          simp only [kd, dif_pos hne]
          apply SDistr.eq_of_some_eq
          exact (hf a b (hc a b hne)).choose.right_marginal)
        c.right_marginal d
  }
  -- Show the composed coupling satisfies S
  intro g d hjoint
  -- hjoint: joint_composed (some (g, d)) ≠ 0
  -- This means ∃ (a, b) in support of c.joint such that (g, d) is in support of kd (a, b)
  -- By construction, when (a, b) is in support, kd uses a coupling satisfying S
  simp only [joint_composed, SDistr.bind, PMF.bind_apply] at hjoint
  by_contra hnotS
  apply hjoint
  rw [ENNReal.tsum_eq_zero]
  intro op
  cases op with
  | none =>
    -- The term for none is: c.joint none * (kd at none, but none is not a pair)
    simp [SDistr.fail, PMF.pure_apply]
  | some p =>
    -- For each pair p = (a, b), if c.joint(a,b) = 0, the term is 0
    -- If c.joint(a,b) ≠ 0, then kd uses a coupling satisfying S,
    -- so kd(g,d) ≠ 0 implies S g d, contradicting hnotS
    by_cases hcjoint : c.joint (some p) = 0
    · simp [hcjoint]
    · -- c.joint (some p) ≠ 0, so kd p uses the coupling from hf
      simp only [kd]
      rw [dif_pos hcjoint]
      -- Let cf be the coupling from hf
      let cf := (hf p.1 p.2 (hc p.1 p.2 hcjoint)).choose
      have hcf_sat := (hf p.1 p.2 (hc p.1 p.2 hcjoint)).choose_spec
      -- cf.satisfies S, so if cf.joint (some (g, d)) ≠ 0, then S g d
      by_cases hcfjoint : cf.joint (some (g, d)) = 0
      · -- cf.joint (some (g,d)) = 0, so the product is 0
        simp only [mul_eq_zero]
        exact Or.inr hcfjoint
      · -- cf.joint (some (g, d)) ≠ 0 and cf satisfies S, so S g d
        exfalso
        exact hnotS (hcf_sat g d hcfjoint)

/-! ## Specialized lifting lemmas -/

/-- Lifting for pure/return -/
theorem liftR_pure {R : α → β → Prop} {a : α} {b : β}
    (h : R a b) : (SDistr.pure a) ⟨R⟩# (SDistr.pure b) := by
  -- Construct coupling that puts all mass on (a, b)
  use {
    joint := SDistr.pure (a, b)
    left_marginal := fun a' => by
      -- (SDistr.pure (a, b)).bind (fun p => SDistr.pure p.1)
      -- = SDistr.pure (a, b).1 = SDistr.pure a  (by pure_bind)
      rw [SDistr.pure_bind]
      -- Now: SDistr.pure a (some a') = SDistr.pure a (some a')
    right_marginal := fun b' => by
      rw [SDistr.pure_bind]
  }
  intro a' b' hab
  simp only [SDistr.pure, PMF.pure_apply, Option.some.injEq, Prod.mk.injEq] at hab
  -- In pure (a,b), only (a,b) has nonzero probability
  by_cases heq : (a', b') = (a, b)
  · rw [Prod.mk.injEq] at heq
    rw [heq.1, heq.2]
    exact h
  · have hneq : ¬(some (a', b') = some (a, b)) := by
      simp only [Option.some.injEq]
      exact heq
    simp only [hneq, ↓reduceIte] at hab
    exact absurd rfl hab

/-- Lifting for fail: fail lifts with fail on any relation.
    This is the correct formulation for sub-distributions:
    the coupling joint = fail satisfies both marginal conditions. -/
theorem liftR_fail {R : α → β → Prop} :
    (SDistr.fail : SDistr α) ⟨R⟩# (SDistr.fail : SDistr β) := by
  use {
    joint := SDistr.fail
    left_marginal := fun a => by
      simp only [SDistr.bind_fail, SDistr.fail_apply_some]
    right_marginal := fun b => by
      simp only [SDistr.bind_fail, SDistr.fail_apply_some]
  }
  intro a b hab
  have h : (SDistr.fail : SDistr (α × β)) (some (a, b)) = 0 := SDistr.fail_apply_some (a, b)
  exact absurd h hab

/-- Lifting for fail on left when d₂ = fail.
    For sub-distributions with joint = fail, the right marginal is 0, so
    d₂ must also have 0 probability on all some values. -/
theorem liftR_fail_l {R : α → β → Prop} :
    (SDistr.fail : SDistr α) ⟨R⟩# (SDistr.fail : SDistr β) := liftR_fail

/-- Lifting for fail on right when d₁ = fail.
    For sub-distributions with joint = fail, the left marginal is 0, so
    d₁ must also have 0 probability on all some values. -/
theorem liftR_fail_r {R : α → β → Prop} :
    (SDistr.fail : SDistr α) ⟨R⟩# (SDistr.fail : SDistr β) := liftR_fail

/-- Uniform distributions lift with any bijection -/
theorem liftR_uniform_bij [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α ≃ β) :
    (SDistr.uniform α) ⟨fun a b => f a = b⟩# (SDistr.uniform β) := by
  -- Use the bijection coupling: couple each a with f a
  -- The joint distribution is: uniform α ▹ (fun a => pure (a, f a))
  -- Left marginal: uniform α (by Coupling.fromBij)
  -- Right marginal: uniform α ▹ (fun a => pure (f a)) = uniform β (by bijection preserves uniform)
  -- The proof requires showing that (uniform α).bind (fun a => pure (f a)) = uniform β
  -- which holds because f is a bijection and |α| = |β|
  have h : (SDistr.uniform α).bind (fun a => SDistr.pure (f a)) = SDistr.uniform β :=
    SDistr.uniform_bind_bij f
  -- Now use Coupling.fromBij
  let c := Coupling.fromBij (SDistr.uniform α) f
  -- c couples uniform α with (uniform α).bind (fun a => pure (f a))
  -- By h, this is uniform β
  use {
    joint := c.joint
    left_marginal := c.left_marginal
    right_marginal := fun b => by
      have := c.right_marginal b
      simp only [h] at this
      exact this
  }
  -- Show satisfies: if joint (some (a, b)) ≠ 0, then f a = b
  intro a b hab
  -- joint = (uniform α).bind (fun x => pure (x, f x))
  -- joint (some (a, b)) ≠ 0 means (a, b) = (x, f x) for some x in support
  -- This means b = f a
  simp only [Coupling.fromBij, c, SDistr.bind, PMF.bind_apply] at hab
  by_contra hne
  apply hab
  rw [ENNReal.tsum_eq_zero]
  intro oa
  cases oa with
  | none => simp [SDistr.fail, PMF.pure_apply]
  | some x =>
    simp only [SDistr.pure, PMF.pure_apply]
    have hneq : ¬(some (a, b) = some (x, f x)) := by
      simp only [Option.some.injEq, Prod.mk.injEq, not_and]
      intro hax
      rw [← hax]
      exact fun hfab => hne hfab.symm
    rw [if_neg hneq, mul_zero]

/-- Same uniform distribution lifts with equality -/
theorem liftR_uniform_same [Fintype α] [Nonempty α] :
    (SDistr.uniform α) ⟨Eq⟩# (SDistr.uniform α) :=
  liftR_refl (SDistr.uniform α)

end CatCrypt.Prob
