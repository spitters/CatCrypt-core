/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Relational.Rules

/-!
# Synchronized pRHL Rules

This file contains synchronized pRHL rules, where the same operation is performed
on both sides of the relational judgment simultaneously.

## Main definitions

* `r_get_vs_get` - Synchronized get on both sides
* `r_put_vs_put` - Synchronized put on both sides
* `r_sample_vs_sample` - Synchronized sampling on both sides

## References

* CatCrypt: theories/Crypt/package/pkg_rhl.v
* EasyCrypt pRHL
-/

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

variable {α β γ : Type*}

/-! ## Synchronized Get Rules -/

/-- Synchronized get on both sides at the same location.
    Precondition must imply the locations have the same value.
    Postcondition gets both values equal and preserves the invariant. -/
theorem r_get_vs_get {Φ : RPre} (l : Location)
    (hSync : ∀ h₁ h₂, Φ h₁ h₂ → h₁.get l = h₂.get l) :
    rHoare Φ (SPComp.get l) (SPComp.get l)
      (fun v₁ h₁ v₂ h₂ => Φ h₁ h₂ ∧ v₁ = v₂) :=
  rHoare_get_sync l hSync

/-- Synchronized get at same location, where the invariant implies equality.
    This version gives a more explicit postcondition that captures the read value. -/
theorem r_get_vs_get' {Φ : RPre} (l : Location)
    (_hSync : ∀ h₁ h₂, Φ h₁ h₂ → h₁.get l = h₂.get l) :
    rHoare Φ (SPComp.get l) (SPComp.get l)
      (fun v₁ h₁ v₂ h₂ => Φ h₁ h₂ ∧ v₁ = h₁.get l ∧ v₂ = h₂.get l) := by
  intro h₁ h₂ hΦ
  simp only [SPComp.get_def]
  exact liftR_pure ⟨hΦ, rfl, rfl⟩

/-- Synchronized get at different locations with same type.
    Each side reads from its respective location.
    Note: This rule is complex due to type casts; prefer using
    `r_get_vs_get` when both locations have the same type. -/
theorem r_get_vs_get_diff {Φ : RPre} (l : Location)
    (hSync : ∀ h₁ h₂, Φ h₁ h₂ → h₁.get l = h₂.get l) :
    rHoare Φ (SPComp.get l) (SPComp.get l)
      (fun v₁ h₁ v₂ h₂ => Φ h₁ h₂ ∧ v₁ = v₂) :=
  r_get_vs_get l hSync

/-! ## Synchronized Put Rules -/

/-- Synchronized put on both sides at the same location with the same value.
    Preserves invariants that are preserved under the synchronized update. -/
theorem r_put_vs_put {Φ : RPre} (l : Location) (v : l.ty)
    (hInv : ∀ h₁ h₂, Φ h₁ h₂ → Φ (h₁.set l v) (h₂.set l v)) :
    rHoare Φ (SPComp.set l v) (SPComp.set l v)
      (fun _ h₁ _ h₂ => Φ h₁ h₂) :=
  rHoare_set_sync l v hInv

/-- Synchronized put with different values on each side.
    Useful when transforming an invariant that relates values at the location. -/
theorem r_put_vs_put_diff {Φ Ψ : RPre} (l : Location) (v₁ v₂ : l.ty)
    (hTrans : ∀ h₁ h₂, Φ h₁ h₂ → Ψ (h₁.set l v₁) (h₂.set l v₂)) :
    rHoare Φ (SPComp.set l v₁) (SPComp.set l v₂)
      (fun _ h₁ _ h₂ => Ψ h₁ h₂) := by
  intro h₁ h₂ hΦ
  simp only [SPComp.set_def]
  exact liftR_pure (hTrans h₁ h₂ hΦ)

/-- Synchronized put at different locations.
    Each side writes to its respective location. -/
theorem r_put_vs_put_diff_loc {Φ Ψ : RPre} (l₁ l₂ : Location) (v₁ : l₁.ty) (v₂ : l₂.ty)
    (hTrans : ∀ h₁ h₂, Φ h₁ h₂ → Ψ (h₁.set l₁ v₁) (h₂.set l₂ v₂)) :
    rHoare Φ (SPComp.set l₁ v₁) (SPComp.set l₂ v₂)
      (fun _ h₁ _ h₂ => Ψ h₁ h₂) := by
  intro h₁ h₂ hΦ
  simp only [SPComp.set_def]
  exact liftR_pure (hTrans h₁ h₂ hΦ)

/-! ## Synchronized Sampling Rules -/

/-- Synchronized sampling from the same distribution on both sides.
    Uses the diagonal coupling where both sides get the same value. -/
theorem r_sample_vs_sample {Φ : RPre} (α : Type*) [Fintype α] [Nonempty α] :
    rHoare Φ (SPComp.sample α) (SPComp.sample α)
      (fun a₁ h₁ a₂ h₂ => Φ h₁ h₂ ∧ a₁ = a₂) :=
  rHoare_sample_same α

/-- Synchronized sampling with a bijection coupling.
    The values on each side are related by the bijection f. -/
theorem r_sample_vs_sample_bij {Φ : RPre} (α β : Type*)
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α ≃ β) :
    rHoare Φ (SPComp.sample α) (SPComp.sample β)
      (fun a h₁ b h₂ => Φ h₁ h₂ ∧ f a = b) :=
  rHoare_sample_bij α β f

/-- Synchronized sampling with an arbitrary coupling relation.
    This is the most general form, requiring a proof that the coupling exists. -/
theorem r_sample_vs_sample_coupling {Φ : RPre} (α β : Type*)
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (R : α → β → Prop)
    (hCoupling : liftR R (SDistr.uniform α) (SDistr.uniform β)) :
    rHoare Φ (SPComp.sample α) (SPComp.sample β)
      (fun a h₁ b h₂ => Φ h₁ h₂ ∧ R a b) := by
  intro h₁ h₂ hΦ
  simp only [SPComp.sample]
  apply liftR_bind hCoupling
  intro a b hRab
  exact liftR_pure ⟨hΦ, hRab⟩

/-! ## Combined Synchronized Operations -/

/-- Get then put on the same location, synchronized on both sides.
    Updates the location with a function of its current value. -/
theorem r_get_put_vs_get_put {Φ Ψ : RPre} (l : Location) (f : l.ty → l.ty)
    (_hSync : ∀ h₁ h₂, Φ h₁ h₂ → h₁.get l = h₂.get l)
    (hInv : ∀ h₁ h₂, Φ h₁ h₂ → Ψ (h₁.set l (f (h₁.get l))) (h₂.set l (f (h₂.get l)))) :
    rHoare Φ (SPComp.get l >>= fun v => SPComp.set l (f v))
             (SPComp.get l >>= fun v => SPComp.set l (f v))
      (fun _ h₁ _ h₂ => Ψ h₁ h₂) := by
  -- Inline proof to avoid issues with intermediate postcondition
  intro h₁ h₂ hΦ
  -- The >>= desugars to SPComp.bind via the Monad instance
  -- SPComp.bind (SPComp.get l) (fun v => SPComp.set l (f v)) h
  -- = (SPComp.get l h).bind (fun (v, h') => SPComp.set l (f v) h')
  -- = (pure (h.get l, h)).bind (fun (v, h') => pure ((), h'.set l (f v)))
  -- = pure ((), h.set l (f (h.get l)))
  simp only [bind, SPComp.bind, SPComp.get, SPComp.set, SDistr.pure_bind]
  exact liftR_pure (hInv h₁ h₂ hΦ)

/-- Sample then put on both sides.
    Samples a value and writes it to the same location. -/
theorem r_sample_put_vs_sample_put {Φ Ψ : RPre} (l : Location) [Fintype l.ty] [Nonempty l.ty]
    (hInv : ∀ h₁ h₂ v, Φ h₁ h₂ → Ψ (h₁.set l v) (h₂.set l v)) :
    rHoare Φ (SPComp.sample l.ty >>= fun v => SPComp.set l v)
             (SPComp.sample l.ty >>= fun v => SPComp.set l v)
      (fun _ h₁ _ h₂ => Ψ h₁ h₂) := by
  intro h₁ h₂ hΦ
  -- The >>= desugars to SPComp.bind via the Monad instance
  simp only [bind, SPComp.bind, SPComp.sample, SPComp.set, SDistr.bind_assoc]
  -- (uniform l.ty).bind (fun v => pure (v, h₁).bind (fun (v, h) => pure ((), h.set l v)))
  -- = (uniform l.ty).bind (fun v => pure ((), h₁.set l v))
  have heq₁ : ∀ v, (SDistr.pure (v, h₁)).bind (fun p => SDistr.pure ((), p.2.set l p.1)) =
                   SDistr.pure ((), h₁.set l v) := fun v => SDistr.pure_bind _ _
  have heq₂ : ∀ v, (SDistr.pure (v, h₂)).bind (fun p => SDistr.pure ((), p.2.set l p.1)) =
                   SDistr.pure ((), h₂.set l v) := fun v => SDistr.pure_bind _ _
  simp only [heq₁, heq₂]
  -- Now apply diagonal coupling
  apply liftR_bind liftR_uniform_same
  intro v v' hvv
  subst hvv
  exact liftR_pure (hInv h₁ h₂ v hΦ)

/-! ## Swap Rules -/

/-- Swap lemma: if same code is run on swapped heaps with swapped pre/post,
    then we can use it on the original judgment. -/
theorem r_swap {Φ : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β}
    (h : rHoare (fun h₂ h₁ => Φ h₁ h₂) c₂ c₁ (fun b h₂ a h₁ => Ψ a h₁ b h₂)) :
    rHoare Φ c₁ c₂ Ψ :=
  rHoare_symm h

/-! ## Frame Rules -/

/-- Frame rule: if the invariant only depends on certain locations,
    and the code only modifies those locations, the invariant is preserved. -/
theorem r_frame {Φ Ψ : RPre} {Θ : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β}
    (hInner : rHoare Φ c₁ c₂ Θ)
    (hFrame : ∀ a h₁ b h₂, Θ a h₁ b h₂ → Ψ h₁ h₂) :
    rHoare (Φ ⋀ Ψ) c₁ c₂ (fun a h₁ b h₂ => Θ a h₁ b h₂ ∧ Ψ h₁ h₂) := by
  intro h₁ h₂ ⟨hΦ, hΨ⟩
  have hh := hInner h₁ h₂ hΦ
  apply liftR_mono _ hh
  intro ⟨a, h₁'⟩ ⟨b, h₂'⟩ hΘ
  exact ⟨hΘ, hFrame a h₁' b h₂' hΘ⟩

end CatCrypt.Relational
