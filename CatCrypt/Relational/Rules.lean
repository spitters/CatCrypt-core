/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Relational.Judgment
import CatCrypt.Crypto.Advantage

/-!
# pRHL Proof Rules

This file contains the core proof rules for probabilistic relational Hoare logic.
-/

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

variable {α β γ δ : Type*}

/-! ## Structural Rules -/

/-- Consequence rule: strengthen precondition, weaken postcondition -/
theorem rHoare_conseq {Φ Φ' : RPre} {Ψ Ψ' : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β}
    (hPre : ∀ h₁ h₂, Φ' h₁ h₂ → Φ h₁ h₂)
    (hPost : ∀ a₁ h₁ a₂ h₂, Ψ a₁ h₁ a₂ h₂ → Ψ' a₁ h₁ a₂ h₂)
    (h : rHoare Φ c₁ c₂ Ψ) :
    rHoare Φ' c₁ c₂ Ψ' := by
  intro h₁ h₂ hΦ'
  have hh := h h₁ h₂ (hPre h₁ h₂ hΦ')
  exact liftR_mono (fun p₁ p₂ hp => hPost p₁.1 p₁.2 p₂.1 p₂.2 hp) hh

/-- Symmetry rule -/
theorem rHoare_symm {Φ : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c₂ : SPComp β}
    (h : rHoare (fun h₁ h₂ => Φ h₂ h₁) c₂ c₁ (fun a₂ h₂ a₁ h₁ => Ψ a₁ h₁ a₂ h₂)) :
    rHoare Φ c₁ c₂ Ψ := by
  intro h₁ h₂ hΦ
  -- h gives us a coupling of (c₂ h₂) and (c₁ h₁) satisfying swapped postcondition
  have hh := h h₂ h₁ hΦ
  -- Use liftR_symm to get a coupling of (c₁ h₁) and (c₂ h₂)
  have hsym := liftR_symm hh
  exact liftR_mono (fun p₁ p₂ hp => hp) hsym

/-! ## Return Rules -/

/-- Return rule: pure values with postcondition derivable from precondition -/
theorem rHoare_ret {Φ : RPre} {a : α} {b : β} {Ψ : RPost α β}
    (h : ∀ h₁ h₂, Φ h₁ h₂ → Ψ a h₁ b h₂) :
    rHoare Φ (pure a : SPComp α) (pure b : SPComp β) Ψ := by
  intro h₁ h₂ hΦ
  exact liftR_pure (h h₁ h₂ hΦ)

/-- Return same value on both sides preserves precondition and establishes equality -/
theorem rHoare_ret_same {Φ : RPre} {a : α} :
    rHoare Φ (pure a : SPComp α) (pure a : SPComp α) (fun a₁ h₁ a₂ h₂ => Φ h₁ h₂ ∧ a₁ = a₂) := by
  apply rHoare_ret
  intro h₁ h₂ hΦ
  exact ⟨hΦ, rfl⟩

/-! ## Bind Rule -/

/-- Bind rule: sequential composition of judgments -/
theorem rHoare_bind {Φ : RPre} {Ψ : RPost α β} {Θ : RPost γ δ}
    {c₁ : SPComp α} {c₂ : SPComp β}
    {f₁ : α → SPComp γ} {f₂ : β → SPComp δ}
    (hc : rHoare Φ c₁ c₂ Ψ)
    (hf : ∀ a b, rHoare (fun h₁ h₂ => Ψ a h₁ b h₂) (f₁ a) (f₂ b) Θ) :
    rHoare Φ (c₁.bind f₁) (c₂.bind f₂) Θ := by
  intro h₁ h₂ hΦ
  -- Get coupling for first computation: (c₁ h₁) ⟨R_Ψ⟩# (c₂ h₂)
  -- where R_Ψ (a₁, h₁') (a₂, h₂') = Ψ a₁ h₁' a₂ h₂'
  have hc' := hc h₁ h₂ hΦ
  -- Use liftR_bind: need to provide continuations and their coupling proof
  -- SPComp.bind c f h = (c h).bind (fun (a, h') => f a h')
  simp only [SPComp.bind_def]
  -- Apply liftR_bind with:
  -- - d₁ = c₁ h₁
  -- - d₂ = c₂ h₂
  -- - f₁' = fun (a, h') => f₁ a h'
  -- - f₂' = fun (b, h') => f₂ b h'
  -- - R = fun (a₁, h₁') (a₂, h₂') => Ψ a₁ h₁' a₂ h₂'
  -- - S = fun (g₁, h₁') (g₂, h₂') => Θ g₁ h₁' g₂ h₂'
  apply liftR_bind hc'
  -- For the continuation, given (a, h₁') and (b, h₂') with Ψ a h₁' b h₂',
  -- show (f₁ a h₁') ⟨...⟩# (f₂ b h₂')
  intro ⟨a, h₁'⟩ ⟨b, h₂'⟩ hΨ
  -- hΨ : Ψ a h₁' b h₂'
  -- Apply hf a b to get rHoare, then specialize to h₁', h₂'
  exact hf a b h₁' h₂' hΨ

/-! ## Reflexivity and Transitivity -/

/-- Reflexivity: same code with equal heaps gives equal results -/
theorem rHoare_refl (c : SPComp α) :
    rHoare eqPre c c eqPost := by
  intro h₁ h₂ heq
  simp only [eqPre] at heq
  subst heq
  -- Use diagonal coupling
  have := liftR_refl (c h₁)
  apply liftR_mono _ this
  intro ⟨a₁, h₁'⟩ ⟨a₂, h₂'⟩ heq'
  simp only [eqPost, Prod.mk.injEq] at heq' ⊢ ; exact heq'

/-- Transitivity for equal-heap coupling.

When composing through an intermediate computation, if:
- c₁ and c₂ produce equal results with equal heaps
- c₂ and c₃ produce equal results with equal heaps
Then c₁ and c₃ also produce equal results with equal heaps.

This is used in hybrid argument proofs where we compose through intermediate games. -/
theorem rHoare_trans (c₁ c₂ c₃ : SPComp α)
    (h₁₂ : rHoare eqPre c₁ c₂ eqPost)
    (h₂₃ : rHoare eqPre c₂ c₃ eqPost) :
    rHoare eqPre c₁ c₃ eqPost := by
  intro h₁ h₃ heq
  simp only [eqPre] at heq
  subst heq
  -- From h₁₂: c₁ h₁ ⟨Eq⟩# c₂ h₁ (with eqPost on pairs)
  -- From h₂₃: c₂ h₁ ⟨Eq⟩# c₃ h₁ (with eqPost on pairs)
  -- By liftR_trans_eq: c₁ h₁ ⟨Eq⟩# c₃ h₁
  have hc₁₂ := h₁₂ h₁ h₁ rfl
  have hc₂₃ := h₂₃ h₁ h₁ rfl
  -- Convert from eqPost relation to Eq relation on pairs
  have hc₁₂' : (c₁ h₁) ⟨Eq⟩# (c₂ h₁) := by
    apply liftR_mono _ hc₁₂
    intro ⟨a₁, h₁'⟩ ⟨a₂, h₂'⟩ heqpost
    simp only [eqPost, Prod.mk.injEq] at heqpost ; exact Prod.ext heqpost.1 heqpost.2
  have hc₂₃' : (c₂ h₁) ⟨Eq⟩# (c₃ h₁) := by
    apply liftR_mono _ hc₂₃
    intro ⟨a₁, h₁'⟩ ⟨a₂, h₂'⟩ heqpost
    simp only [eqPost, Prod.mk.injEq] at heqpost ; exact Prod.ext heqpost.1 heqpost.2
  -- Apply transitivity
  have hc₁₃' := liftR_trans_eq hc₁₂' hc₂₃'
  -- Convert back to eqPost
  apply liftR_mono _ hc₁₃'
  intro ⟨a₁, h₁'⟩ ⟨a₃, h₃'⟩ heq
  simp only [Prod.mk.injEq] at heq
  simp only [eqPost, Prod.mk.injEq] ; exact heq

/-! ## Sampling Rules -/

/-- Same distribution, diagonal coupling -/
theorem rHoare_sample_same {Φ : RPre} (α : Type*) [Fintype α] [Nonempty α] :
    rHoare Φ (SPComp.sample α) (SPComp.sample α)
      (fun a₁ h₁ a₂ h₂ => Φ h₁ h₂ ∧ a₁ = a₂) := by
  intro h₁ h₂ hΦ
  -- SPComp.sample α h = (SDistr.uniform α).bind fun a => SDistr.pure (a, h)
  -- Strategy: use liftR_bind with:
  -- 1. uniform α coupled with uniform α via diagonal (liftR_uniform_same)
  -- 2. continuations coupled via liftR_pure
  simp only [SPComp.sample]
  apply liftR_bind liftR_uniform_same
  -- For each pair (a, a') with a = a', show continuations are coupled
  intro a a' heq
  -- heq : a = a'
  subst heq
  -- Need: (SDistr.pure (a, h₁)) ⟨R⟩# (SDistr.pure (a, h₂))
  -- where R = fun (v₁, h₁') (v₂, h₂') => Φ h₁' h₂' ∧ v₁ = v₂
  apply liftR_pure
  -- Goal: Φ h₁ h₂ ∧ a = a
  exact ⟨hΦ, rfl⟩

/-- Bijection coupling -/
theorem rHoare_sample_bij {Φ : RPre} (α β : Type*)
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α ≃ β) :
    rHoare Φ (SPComp.sample α) (SPComp.sample β)
      (fun a h₁ b h₂ => Φ h₁ h₂ ∧ f a = b) := by
  intro h₁ h₂ hΦ
  -- SPComp.sample α h = (SDistr.uniform α).bind fun a => SDistr.pure (a, h)
  -- Strategy: use liftR_bind with:
  -- 1. uniform α coupled with uniform β via bijection f (liftR_uniform_bij)
  -- 2. continuations coupled via liftR_pure
  simp only [SPComp.sample]
  apply liftR_bind (liftR_uniform_bij f)
  -- For each pair (a, b) with f a = b, show continuations are coupled
  intro a b hfab
  -- hfab : f a = b
  -- Need: (SDistr.pure (a, h₁)) ⟨R⟩# (SDistr.pure (b, h₂))
  -- where R = fun (v₁, h₁') (v₂, h₂') => Φ h₁' h₂' ∧ f v₁ = v₂
  apply liftR_pure
  -- Goal: Φ h₁ h₂ ∧ f a = b
  exact ⟨hΦ, hfab⟩

/-- One-sided sample on the left.

    Key idea: Use averaging coupling.
    - For each sampled value a, we have a coupling from `h a`
    - Rewrite right side as (uniform σ).bind (fun _ => c₂ h₂) using uniform_bind_const
    - Apply liftR_bind with the diagonal coupling on σ -/
theorem rHoare_sample_l {σ τ ρ : Type*} {Φ : RPre} {Ψ : RPost τ ρ}
    [Fintype σ] [Nonempty σ]
    {c₂ : SPComp ρ} {f : σ → SPComp τ}
    (h : ∀ a, rHoare Φ (f a) c₂ Ψ) :
    rHoare Φ (SPComp.bind (SPComp.sample σ) f) c₂ Ψ := by
  intro h₁ h₂ hΦ
  -- Simplify the left side
  simp only [SPComp.bind, SPComp.sample, SDistr.bind_assoc]
  have heq_l : (SDistr.uniform σ).bind (fun a => (SDistr.pure (a, h₁)).bind
      (fun p => f p.1 p.2)) = (SDistr.uniform σ).bind (fun a => f a h₁) := by
    apply SDistr.bind_congr_support
    intro a _
    simp only [SDistr.pure_bind]
  rw [heq_l, ← SDistr.uniform_bind_const (α := σ) (c₂ h₂)]
  -- Now both sides are binds from uniform σ
  -- Apply liftR_bind with diagonal coupling on σ
  apply liftR_bind (R := Eq)
  · exact liftR_refl (SDistr.uniform σ)
  · intro a a' heq
    subst heq
    -- Now show: (f a h₁) ⟨Ψ'⟩# (c₂ h₂)
    exact h a h₁ h₂ hΦ

/-- One-sided sample on the right.

    Key idea: Use averaging coupling (symmetric to sample_l). -/
theorem rHoare_sample_r {σ τ ρ : Type*} {Φ : RPre} {Ψ : RPost ρ τ}
    [Fintype σ] [Nonempty σ]
    {c₁ : SPComp ρ} {f : σ → SPComp τ}
    (h : ∀ a, rHoare Φ c₁ (f a) Ψ) :
    rHoare Φ c₁ (SPComp.bind (SPComp.sample σ) f) Ψ := by
  intro h₁ h₂ hΦ
  -- Simplify the right side
  simp only [SPComp.bind, SPComp.sample, SDistr.bind_assoc]
  have heq_r : (SDistr.uniform σ).bind (fun a => (SDistr.pure (a, h₂)).bind
      (fun p => f p.1 p.2)) = (SDistr.uniform σ).bind (fun a => f a h₂) := by
    apply SDistr.bind_congr_support
    intro a _
    simp only [SDistr.pure_bind]
  rw [heq_r, ← SDistr.uniform_bind_const (α := σ) (c₁ h₁)]
  -- Now both sides are binds from uniform σ
  apply liftR_bind (R := Eq)
  · exact liftR_refl (SDistr.uniform σ)
  · intro a a' heq
    subst heq
    exact h a h₁ h₂ hΦ

/-! ## State Rules -/

/-- Synchronized get: same location, synchronized values -/
theorem rHoare_get_sync {Φ : RPre} (l : Location)
    (hSync : ∀ h₁ h₂, Φ h₁ h₂ → h₁.get l = h₂.get l) :
    rHoare Φ (SPComp.get l) (SPComp.get l)
      (fun v₁ h₁ v₂ h₂ => Φ h₁ h₂ ∧ v₁ = v₂) := by
  intro h₁ h₂ hΦ
  simp only [SPComp.get_def]
  apply liftR_pure
  constructor
  · exact hΦ
  · exact hSync h₁ h₂ hΦ

/-- Synchronized set: same location and value -/
theorem rHoare_set_sync {Φ : RPre} (l : Location) (v : l.ty)
    (hInv : ∀ h₁ h₂, Φ h₁ h₂ → Φ (h₁.set l v) (h₂.set l v)) :
    rHoare Φ (SPComp.set l v) (SPComp.set l v)
      (fun _ h₁ _ h₂ => Φ h₁ h₂) := by
  intro h₁ h₂ hΦ
  simp only [SPComp.set_def]
  apply liftR_pure
  exact hInv h₁ h₂ hΦ

/-- One-sided get on the left.
    Note: β is constrained to Type (universe 0) since l.ty : Type. -/
theorem rHoare_get_l {β γ : Type} {Φ : RPre} {Ψ : RPost β γ}
    (l : Location) {c₂ : SPComp γ} {f : l.ty → SPComp β}
    (h : ∀ v, rHoare (fun h₁ h₂ => Φ h₁ h₂ ∧ h₁.get l = v) (f v) c₂ Ψ) :
    rHoare Φ (SPComp.get l >>= f) c₂ Ψ := by
  intro h₁ h₂ hΦ
  have hv := h (h₁.get l) h₁ h₂ ⟨hΦ, rfl⟩
  have heq : (SPComp.get l >>= f) h₁ = f (h₁.get l) h₁ := by
    simp only [bind, SPComp.bind, SPComp.get, SDistr.pure_bind]
  rw [heq]
  exact hv

/-- One-sided get on the right.
    Note: β is constrained to Type (universe 0) since l.ty : Type. -/
theorem rHoare_get_r {β γ : Type} {Φ : RPre} {Ψ : RPost γ β}
    (l : Location) {c₁ : SPComp γ} {f : l.ty → SPComp β}
    (h : ∀ v, rHoare (fun h₁ h₂ => Φ h₁ h₂ ∧ h₂.get l = v) c₁ (f v) Ψ) :
    rHoare Φ c₁ (SPComp.get l >>= f) Ψ := by
  intro h₁ h₂ hΦ
  have hv := h (h₂.get l) h₁ h₂ ⟨hΦ, rfl⟩
  have heq : (SPComp.get l >>= f) h₂ = f (h₂.get l) h₂ := by
    simp only [bind, SPComp.bind, SPComp.get, SDistr.pure_bind]
  rw [heq]
  exact hv

/-- One-sided put on the left -/
theorem rHoare_put_l {τ ρ : Type*} {Φ : RPre} {Ψ : RPost τ ρ}
    (l : Location) (v : l.ty) {c₂ : SPComp ρ} {f : Unit → SPComp τ}
    (h : rHoare (fun h₁ h₂ => Φ h₁ h₂) (f ()) c₂ Ψ) :
    rHoare (fun h₁ h₂ => Φ (h₁.set l v) h₂) (SPComp.bind (SPComp.set l v) f) c₂ Ψ := by
  intro h₁ h₂ hΦ
  -- hΦ : Φ (h₁.set l v) h₂
  -- Show (set l v >>= f) h₁ = f () (h₁.set l v)
  have heq : (SPComp.bind (SPComp.set l v) f) h₁ = f () (h₁.set l v) := by
    simp only [SPComp.bind, SPComp.set, SDistr.pure_bind]
  rw [heq]
  exact h (h₁.set l v) h₂ hΦ

/-- One-sided put on the right -/
theorem rHoare_put_r {τ ρ : Type*} {Φ : RPre} {Ψ : RPost ρ τ}
    (l : Location) (v : l.ty) {c₁ : SPComp ρ} {f : Unit → SPComp τ}
    (h : rHoare (fun h₁ h₂ => Φ h₁ h₂) c₁ (f ()) Ψ) :
    rHoare (fun h₁ h₂ => Φ h₁ (h₂.set l v)) c₁ (SPComp.bind (SPComp.set l v) f) Ψ := by
  intro h₁ h₂ hΦ
  -- hΦ : Φ h₁ (h₂.set l v)
  -- Show (set l v >>= f) h₂ = f () (h₂.set l v)
  have heq : (SPComp.bind (SPComp.set l v) f) h₂ = f () (h₂.set l v) := by
    simp only [SPComp.bind, SPComp.set, SDistr.pure_bind]
  rw [heq]
  exact h h₁ (h₂.set l v) hΦ

/-! ## Failure and Assertion Rules -/

/-- Failure on both sides: when both programs fail, any postcondition holds vacuously.
    Note: With coupling-based semantics, failure on one side requires failure on the other
    for a valid coupling to exist (since marginals must match). -/
theorem rHoare_fail {Φ : RPre} {Ψ : RPost α β} :
    rHoare Φ (SPComp.fail : SPComp α) (SPComp.fail : SPComp β) Ψ := by
  intro h₁ h₂ _
  simp only [SPComp.fail]
  exact liftR_fail

/-- Assertion: if precondition implies P, assertion succeeds -/
theorem rHoare_assert {Φ : RPre} (P : Prop) [Decidable P]
    (hP : ∀ h₁ h₂, Φ h₁ h₂ → P) :
    rHoare Φ (SPComp.assert P) (SPComp.assert P) (fun _ h₁ _ h₂ => Φ h₁ h₂) := by
  intro h₁ h₂ hΦ
  simp only [SPComp.assert]
  have hp := hP h₁ h₂ hΦ
  simp only [hp, ↓reduceIte]
  simp only [SPComp.pure_def]
  apply liftR_pure
  exact hΦ

/-! ## Conditional Rules -/

/-- Synchronized conditional: when both sides branch on the same `Bool` value,
    prove each branch separately.

    This is the standard pRHL `if` rule. After a synchronized `get`, both
    sides evaluate the same condition, so we case-split on the shared value. -/
theorem rHoare_ite {Φ : RPre} {Ψ : RPost α β}
    (b : Bool)
    {c₁t c₁f : SPComp α} {c₂t c₂f : SPComp β}
    (ht : rHoare Φ c₁t c₂t Ψ)
    (hf : rHoare Φ c₁f c₂f Ψ) :
    rHoare Φ (if b then c₁t else c₁f) (if b then c₂t else c₂f) Ψ := by
  cases b <;> assumption

/-- Synchronized conditional with different conditions: when conditions agree
    (provable from equality or other means), prove each branch separately. -/
theorem rHoare_if {Φ : RPre} {Ψ : RPost α β}
    {b₁ b₂ : Bool}
    {c₁t c₁f : SPComp α} {c₂t c₂f : SPComp β}
    (hb : b₁ = b₂)
    (ht : rHoare Φ c₁t c₂t Ψ)
    (hf : rHoare Φ c₁f c₂f Ψ) :
    rHoare Φ (if b₁ then c₁t else c₁f) (if b₂ then c₂t else c₂f) Ψ := by
  subst hb; cases b₁ <;> assumption

/-- Synchronized decidable conditional: both sides branch on the same
    decidable proposition `P`. The branch proofs may depend on `P` or `¬P`. -/
theorem rHoare_dite {Φ : RPre} {Ψ : RPost α β}
    (P : Prop) [Decidable P]
    {c₁t : P → SPComp α} {c₁f : ¬P → SPComp α}
    {c₂t : P → SPComp β} {c₂f : ¬P → SPComp β}
    (ht : ∀ hp : P, rHoare Φ (c₁t hp) (c₂t hp) Ψ)
    (hf : ∀ hp : ¬P, rHoare Φ (c₁f hp) (c₂f hp) Ψ) :
    rHoare Φ (dite P c₁t c₁f) (dite P c₂t c₂f) Ψ := by
  split
  · exact ht ‹_›
  · exact hf ‹_›

/-! ## Swap Rules

These rules allow reordering independent operations in a computation.
This is useful when the order of operations on the left and right sides differ.
-/

/-- Swap on left: if two SPComp programs are equal (as functions from Heap),
    we can replace one with the other on the left side of a relational judgment. -/
theorem rHoare_swap_lhs {Φ : RPre} {Ψ : RPost γ δ}
    {c₁ c₁' : SPComp γ} {c₂ : SPComp δ}
    (heq : ∀ h, c₁ h = c₁' h)
    (h : rHoare Φ c₁' c₂ Ψ) :
    rHoare Φ c₁ c₂ Ψ := by
  intro h₁ h₂ hΦ
  rw [heq]
  exact h h₁ h₂ hΦ

/-- Swap on right: symmetric to swap_lhs -/
theorem rHoare_swap_rhs {Φ : RPre} {Ψ : RPost γ δ}
    {c₁ : SPComp γ} {c₂ c₂' : SPComp δ}
    (heq : ∀ h, c₂ h = c₂' h)
    (h : rHoare Φ c₁ c₂' Ψ) :
    rHoare Φ c₁ c₂ Ψ := by
  intro h₁ h₂ hΦ
  rw [heq]
  exact h h₁ h₂ hΦ

/-- Swap two consecutive samples.
    The order of two independent sampling operations can be exchanged
    because sampling from independent distributions commutes.

    Uses the Fubini property for finite distributions. -/
theorem SPComp.swap_sample_sample (α β γ : Type) [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α → β → SPComp γ) (h : Heap) :
    (do let x ← SPComp.sample α; let y ← SPComp.sample β; f x y) h =
    (do let y ← SPComp.sample β; let x ← SPComp.sample α; f x y) h := by
  simp only [SPComp.monad_bind_eq, SPComp.bind_def, SPComp.sample]
  rw [SDistr.bind_assoc, SDistr.bind_assoc]
  -- Simplify the inner binds
  conv_lhs =>
    arg 2; ext a
    rw [SDistr.pure_bind, SDistr.bind_assoc]
    arg 2; ext b
    rw [SDistr.pure_bind]
  conv_rhs =>
    arg 2; ext b
    rw [SDistr.pure_bind, SDistr.bind_assoc]
    arg 2; ext a
    rw [SDistr.pure_bind]
  -- Both sides are now:
  -- LHS: (uniform α).bind (fun a => (uniform β).bind (fun b => f a b h))
  -- RHS: (uniform β).bind (fun b => (uniform α).bind (fun a => f a b h))
  -- Use SDistr.bind_comm to swap the order
  rw [SDistr.bind_comm]

/-- Swap sample followed by get on the left.
    Sample and get from a location commute because sampling doesn't affect the heap
    and get doesn't affect the distribution. -/
theorem SPComp.swap_sample_get (α β : Type) [Fintype α] [Nonempty α]
    (l : Location) (f : α → l.ty → SPComp β) (h : Heap) :
    (do let x ← SPComp.sample α; let v ← SPComp.get l; f x v) h =
    (do let v ← SPComp.get l; let x ← SPComp.sample α; f x v) h := by
  simp only [SPComp.monad_bind_eq, SPComp.bind_def, SPComp.sample, SPComp.get]
  rw [SDistr.bind_assoc]
  conv_lhs =>
    arg 2; ext a
    rw [SDistr.pure_bind]
    rw [SDistr.pure_bind]
  -- LHS: (uniform α).bind (fun a => f a (h.get l) h)
  -- RHS: (pure (h.get l, h)).bind (fun (v, h') => (sample α h').bind ...)
  rw [SDistr.pure_bind]
  simp only [SPComp.bind, SPComp.sample]
  rw [SDistr.bind_assoc]
  conv_rhs =>
    arg 2; ext a
    rw [SDistr.pure_bind]
  -- Both are now: (uniform α).bind (fun a => f a (h.get l) h)

/-- Swap get followed by sample on the left.
    Get and sample commute because get is deterministic and doesn't affect
    the distribution of sample. -/
theorem SPComp.swap_get_sample (α β : Type) [Fintype α] [Nonempty α]
    (l : Location) (f : l.ty → α → SPComp β) (h : Heap) :
    (do let v ← SPComp.get l; let x ← SPComp.sample α; f v x) h =
    (do let x ← SPComp.sample α; let v ← SPComp.get l; f v x) h := by
  rw [SPComp.swap_sample_get]
  -- The two sides are now the same up to argument order in f

/-- Swap two consecutive gets from different locations.
    Get operations from independent locations can be reordered. -/
theorem SPComp.swap_get_get (α : Type) (l₁ l₂ : Location)
    (f : l₁.ty → l₂.ty → SPComp α) (h : Heap) :
    (do let v₁ ← SPComp.get l₁; let v₂ ← SPComp.get l₂; f v₁ v₂) h =
    (do let v₂ ← SPComp.get l₂; let v₁ ← SPComp.get l₁; f v₁ v₂) h := by
  simp only [SPComp.monad_bind_eq, SPComp.bind_def, SPComp.get_def, SDistr.pure_bind]
  -- Both sides equal f (h.get l₁) (h.get l₂) h

/-- Swap set followed by sample.
    Set and sample commute because set is deterministic and sample doesn't depend on heap. -/
theorem SPComp.swap_set_sample (α β : Type) [Fintype α] [Nonempty α]
    (l : Location) (v : l.ty) (f : α → SPComp β) (h : Heap) :
    (do SPComp.set l v; let x ← SPComp.sample α; f x) h =
    (do let x ← SPComp.sample α; SPComp.set l v; f x) h := by
  simp only [SPComp.monad_bind_eq, SPComp.bind_def, SPComp.set_def, SPComp.sample, SDistr.pure_bind,
             SDistr.bind_assoc]
  -- Both sides simplify to: (uniform α).bind (fun a => f a (h.set l v))

/-- Swap sample followed by set.
    Sample and set commute because sample doesn't affect the heap value being set. -/
theorem SPComp.swap_sample_set (α β : Type) [Fintype α] [Nonempty α]
    (l : Location) (v : l.ty) (f : α → SPComp β) (h : Heap) :
    (do let x ← SPComp.sample α; SPComp.set l v; f x) h =
    (do SPComp.set l v; let x ← SPComp.sample α; f x) h :=
  (SPComp.swap_set_sample α β l v f h).symm

/-- Swap set followed by get from a different location.
    Set and get from independent locations can be reordered. -/
theorem SPComp.swap_set_get (α : Type) (l₁ l₂ : Location) (v : l₁.ty)
    (hne : l₁.id ≠ l₂.id) (f : l₂.ty → SPComp α) (h : Heap) :
    (do SPComp.set l₁ v; let x ← SPComp.get l₂; f x) h =
    (do let x ← SPComp.get l₂; SPComp.set l₁ v; f x) h := by
  simp only [SPComp.monad_bind_eq, SPComp.bind_def, SPComp.set_def, SPComp.get_def, SDistr.pure_bind]
  -- LHS: f (h.set l₁ v).get l₂) (h.set l₁ v)
  -- RHS: f (h.get l₂) (h.set l₁ v)
  -- Need: (h.set l₁ v).get l₂ = h.get l₂ for l₁.id ≠ l₂.id
  congr 1
  exact Heap.get_set_other h l₁ l₂ v hne

/-- Swap get followed by set to a different location.
    Get and set to independent locations can be reordered. -/
theorem SPComp.swap_get_set (α : Type) (l₁ l₂ : Location) (v : l₂.ty)
    (hne : l₁.id ≠ l₂.id) (f : l₁.ty → SPComp α) (h : Heap) :
    (do let x ← SPComp.get l₁; SPComp.set l₂ v; f x) h =
    (do SPComp.set l₂ v; let x ← SPComp.get l₁; f x) h := by
  rw [SPComp.swap_set_get (hne := hne.symm)]

/-- Swap two consecutive sets to different locations.
    Set operations to independent locations can be reordered. -/
theorem SPComp.swap_set_set (α : Type) (l₁ l₂ : Location) (v₁ : l₁.ty) (v₂ : l₂.ty)
    (hne : l₁.id ≠ l₂.id) (k : SPComp α) (h : Heap) :
    (do SPComp.set l₁ v₁; SPComp.set l₂ v₂; k) h =
    (do SPComp.set l₂ v₂; SPComp.set l₁ v₁; k) h := by
  simp only [SPComp.monad_bind_eq, SPComp.bind_def, SPComp.set_def, SDistr.pure_bind]
  -- LHS: k ((h.set l₁ v₁).set l₂ v₂)
  -- RHS: k ((h.set l₂ v₂).set l₁ v₁)
  -- Need: (h.set l₁ v₁).set l₂ v₂ = (h.set l₂ v₂).set l₁ v₁ for l₁.id ≠ l₂.id
  congr 1
  exact Heap.set_set_comm h l₁ l₂ v₁ v₂ hne

/-! ## Post-Processing and Factorization

These rules establish key inequalities for security reductions.
The post-processing lemma states that applying the same function
to two distributions cannot increase the advantage of distinguishing them.
-/

open CatCrypt.Crypto

/-- Post-processing lemma: post-processing cannot increase advantage.
    If we apply the same function f to two computations, the advantage
    of distinguishing the results is at most the advantage of distinguishing
    the original computations.

    This is fundamental for reduction proofs: if an adversary can break
    the composed scheme G.bind f, we can use it to break G with at least
    the same advantage.

    **Proof sketch**: The adversary for the composed scheme is A ∘ f.
    By definition, AdvantageA (G₁.bind f) (G₂.bind f) (pure ·) measures
    how well we can distinguish when applying the trivial distinguisher.
    The RHS measures distinguishing G₁ from G₂ using (f · >>= A) as the test. -/
theorem advantage_data_processing {α β : Type}
    (f : α → SPComp β) (G₁ G₂ : SPComp α) (A : β → SPComp Bool) :
    AdvantageA (G₁.bind f) (G₂.bind f) A ≤ AdvantageA G₁ G₂ (fun x => (f x).bind A) := by
  -- Both sides are equal by associativity of bind:
  -- LHS = Advantage ((G₁.bind f).bind A) ((G₂.bind f).bind A)
  --     = Advantage (G₁.bind (fun x => (f x).bind A)) (G₂.bind (fun x => (f x).bind A))
  --     = RHS
  unfold AdvantageA
  -- Use bind associativity: (c.bind f).bind g = c.bind (fun a => (f a).bind g)
  rw [SPComp.bind_assoc G₁ f A, SPComp.bind_assoc G₂ f A]
  -- Now both sides are equal

/-- Factorization: rewriting advantage in terms of intermediate computations.

    If two games can be written as the same function applied to different
    base computations, the advantage equals the advantage on the base
    computations with the composed distinguisher.

    This is an equality (not just inequality) because bind is associative. -/
theorem advantage_factorization {α β : Type} (f : α → SPComp β)
    (G₁ G₂ : SPComp α) (A : β → SPComp Bool) :
    AdvantageA (G₁.bind f) (G₂.bind f) A = AdvantageA G₁ G₂ (fun x => (f x).bind A) := by
  unfold AdvantageA
  -- By associativity: (G.bind f).bind A = G.bind (fun x => (f x).bind A)
  rw [SPComp.bind_assoc G₁ f A, SPComp.bind_assoc G₂ f A]

/-- Advantage is symmetric: swapping the games doesn't change the advantage.
    This follows from the symmetric definition using max of both directions. -/
theorem advantage_symm (G₁ G₂ : SPComp Bool) :
    Advantage G₁ G₂ = Advantage G₂ G₁ := by
  unfold Advantage
  rw [max_comm]

/-! ## Contract Rules

These rules establish equality between SPComp programs by eliminating redundant operations.
They are used by contract tactics to simplify code before relational reasoning.
-/

/-- Contract duplicate gets: getting the same location twice in sequence
    is equivalent to getting once and using the value twice.

    `x ← get l; y ← get l; f x y` = `x ← get l; f x x`

    Note: α is constrained to Type (universe 0) since l.ty : Type.
-/
@[simp] theorem contract_get {α : Type} (l : Location) (f : l.ty → l.ty → SPComp α) :
    (do let x ← SPComp.get l; let y ← SPComp.get l; f x y) =
    (do let x ← SPComp.get l; f x x) := by
  funext h
  simp only [SPComp.monad_bind_eq, SPComp.bind_def, SPComp.get_def, SDistr.pure_bind]

/-- Contract duplicate puts: putting to the same location twice in sequence
    is equivalent to just putting the second value.

    `put l v; put l v'; k` = `put l v'; k`

    Note: α is constrained to Type (universe 0) since l.ty : Type.
-/
@[simp] theorem contract_put {α : Type} (l : Location) (v v' : l.ty) (k : SPComp α) :
    (do SPComp.set l v; SPComp.set l v'; k) = (do SPComp.set l v'; k) := by
  funext h
  simp only [SPComp.monad_bind_eq, SPComp.bind_def, SPComp.set_def, SDistr.pure_bind]
  congr 1
  exact Heap.set_set_same h l v v'

/-- Contract put-get: getting a location immediately after putting to it
    returns the value that was put.

    `put l v; x ← get l; f x` = `put l v; f v`

    Note: α is constrained to Type (universe 0) since l.ty : Type.
-/
@[simp] theorem contract_put_get {α : Type} (l : Location) (v : l.ty) (f : l.ty → SPComp α) :
    (do SPComp.set l v; let x ← SPComp.get l; f x) = (do SPComp.set l v; f v) := by
  funext h
  simp only [SPComp.monad_bind_eq, SPComp.bind_def, SPComp.set_def, SPComp.get_def,
             SDistr.pure_bind, Heap.get_set_same]

/-! ## Dead Code Elimination Rules

These rules eliminate unused computations from SPComp programs.
They are used by the ProofFrog-inspired dead code elimination tactics.
-/

/-- Const sample: sampling and ignoring the result is equivalent to identity.

    This lemma is used by dead_sample to eliminate unused samples.
-/
theorem SDistr.bind_const_eq {α β : Type} [Fintype α] [Nonempty α] (d : SDistr β) :
    (SDistr.uniform α).bind (fun _ => d) = d := by
  -- SDistr.uniform α = PMF.map some (PMF.uniformOfFintype α)
  -- SDistr.bind d f = PMF.bind d (fun oa => match oa with some a => f a | none => fail)
  simp only [SDistr.bind, SDistr.uniform]
  -- Use PMF.bind_map: (map f p).bind g = p.bind (g ∘ f)
  rw [PMF.bind_map]
  -- Now we have: (PMF.uniformOfFintype α).bind (fun a => match some a with ...)
  -- The composition simplifies because some a always matches
  conv_lhs =>
    arg 2
    ext a
    simp only [Function.comp_apply]
  -- Use PMF.bind_const
  exact PMF.bind_const (PMF.uniformOfFintype α) d

/-- Dead sample: if a sample result is not used, the sample can be eliminated.

    `let _ ← sample α; k` = `k`

    Note: This is sound because sampling from a uniform distribution and
    discarding the result is equivalent to doing nothing (lossless sampling).
-/
@[simp] theorem dead_sample {α β : Type} [Fintype α] [Nonempty α] (k : SPComp β) :
    (SPComp.sample α).bind (fun _ => k) = k := by
  funext h
  simp only [SPComp.bind_def, SPComp.sample]
  -- (SDistr.uniform α).bind (fun a => SDistr.pure (a, h)).bind (fun p => k p.2)
  rw [SDistr.bind_assoc]
  simp only [SDistr.pure_bind]
  -- (SDistr.uniform α).bind (fun a => k h) = k h
  exact SDistr.bind_const_eq (k h)

/-- Dead get: if a get result is not used, the get can be eliminated.

    `let _ ← get l; k` = `k`

    Note: This is sound because get is a pure read with no side effects.
-/
@[simp] theorem dead_get {α : Type} (l : Location) (k : SPComp α) :
    (SPComp.get l).bind (fun _ => k) = k := by
  funext h
  simp only [SPComp.bind_def, SPComp.get_def, SDistr.pure_bind]

/-- Dead pure: if a pure result is not used, the pure can be eliminated.

    `let _ ← pure v; k` = `k`
-/
@[simp] theorem dead_pure {α β : Type} (v : α) (k : SPComp β) :
    (pure v : SPComp α).bind (fun _ => k) = k := by
  funext h
  -- unfold pure and bind
  -- (pure v : SPComp α) = SPComp.pure v = fun h => SDistr.pure (v, h)
  -- so (pure v).bind f h = (SPComp.pure v h).bind (fun p => f p.1 p.2)
  --                      = (SDistr.pure (v, h)).bind (fun p => f p.1 p.2)
  --                      = f v h
  show ((SPComp.pure v).bind (fun _ => k)) h = k h
  rw [SPComp.bind_def, SPComp.pure_def]
  -- SDistr.pure (v, h).bind (fun x => k x.2) = k h
  rw [SDistr.pure_bind]
  -- Goal is now k h = k h which is rfl

/-! ## Copy Propagation Rules

These rules help with copy propagation by providing lemmas for
substituting known values.
-/

/-- Get followed by using the value: the continuation sees the heap value.

    After `x ← get l`, we know `x = h.get l`. This lemma is used for
    copy propagation where we substitute the known value.
-/
theorem get_value_eq {α : Type} (l : Location) (f : l.ty → SPComp α) (h : Heap) :
    (do let x ← SPComp.get l; f x) h = f (h.get l) h :=
  by simp only [SPComp.monad_bind_eq, SPComp.bind_def, SPComp.get_def, SDistr.pure_bind]

/-- After set, the location has the set value.

    `(set l v; get l)` returns `v`.
-/
theorem set_get_same {α : Type} (l : Location) (v : l.ty) (f : l.ty → SPComp α) :
    (do SPComp.set l v; let x ← SPComp.get l; f x) = (do SPComp.set l v; f v) :=
  contract_put_get l v f

/-! ## Unreachable Code Rules

These rules help identify and eliminate unreachable code paths.
-/

/-- If the precondition is False, any relational judgment holds trivially. -/
theorem rHoare_false {Ψ : RPost α β} {c₁ : SPComp α} {c₂ : SPComp β} :
    rHoare (fun _ _ => False) c₁ c₂ Ψ := by
  intro h₁ h₂ hFalse
  exact False.elim hFalse

/-- If we have an assertion `#assert false`, the code is unreachable. -/
theorem assert_false_unreachable {α : Type} (k : SPComp α) :
    (if false then k else SPComp.fail) = SPComp.fail := rfl

/-- Rewriting on LHS is sound for rHoare when the codes are equal. -/
theorem rHoare_rewrite_lhs {Φ : RPre} {Ψ : RPost α β}
    {c₁ c₁' : SPComp α} {c₂ : SPComp β}
    (heq : c₁ = c₁')
    (h : rHoare Φ c₁' c₂ Ψ) :
    rHoare Φ c₁ c₂ Ψ := by
  rw [heq]; exact h

/-- Rewriting on RHS is sound for rHoare when the codes are equal. -/
theorem rHoare_rewrite_rhs {Φ : RPre} {Ψ : RPost α β}
    {c₁ : SPComp α} {c₂ c₂' : SPComp β}
    (heq : c₂ = c₂')
    (h : rHoare Φ c₁ c₂' Ψ) :
    rHoare Φ c₁ c₂ Ψ := by
  rw [heq]; exact h

/-! ## Combined Coupling Steps

These lemmas combine `rHoare_bind` + `rHoare_sample_bij`/`rHoare_sample_same`
into a single step, eliminating the need for explicit intermediate postconditions.
-/

/-- Combined bijection coupling step.

Combines `rHoare_bind` + `rHoare_sample_bij` + precondition adjustment in one step.
When both sides sample and you have a bijection `f`, this reduces to proving
the continuation for each sampled value `a` with the right side receiving `f a`.

Replaces the common 4-8 line pattern:
```
apply rHoare_bind (Ψ := fun a _ b _ => Φ h₁ h₂ ∧ f a = b)
· exact rHoare_sample_bij α β f
· intro a b
  apply rHoare_conseq ...
```
with a single application. -/
theorem rHoare_bij_step {α β γ δ : Type*} {Φ : RPre} {Ψ : RPost γ δ}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α ≃ β)
    {k₁ : α → SPComp γ} {k₂ : β → SPComp δ}
    (h : ∀ a, rHoare Φ (k₁ a) (k₂ (f a)) Ψ) :
    rHoare Φ (SPComp.bind (SPComp.sample α) k₁) (SPComp.bind (SPComp.sample β) k₂) Ψ := by
  intro h₁ h₂ hΦ
  simp only [SPComp.bind, SPComp.sample, SDistr.bind_assoc, SDistr.pure_bind]
  apply liftR_bind (liftR_uniform_bij f)
  intro a b hab
  subst hab
  exact h a h₁ h₂ hΦ

/-- Bijection step with bare sample on the right side. -/
theorem rHoare_bij_step_bare_r {α β γ : Type*} {Φ : RPre} {Ψ : RPost γ β}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α ≃ β) {k₁ : α → SPComp γ}
    (h : ∀ a, rHoare Φ (k₁ a) (pure (f a)) Ψ) :
    rHoare Φ (SPComp.bind (SPComp.sample α) k₁) (SPComp.sample β) Ψ :=
  SPComp.bind_pure (SPComp.sample β) ▸ rHoare_bij_step f h

/-- Bijection step with bare sample on the left side. -/
theorem rHoare_bij_step_bare_l {α β δ : Type*} {Φ : RPre} {Ψ : RPost α δ}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α ≃ β) {k₂ : β → SPComp δ}
    (h : ∀ a, rHoare Φ (pure a) (k₂ (f a)) Ψ) :
    rHoare Φ (SPComp.sample α) (SPComp.bind (SPComp.sample β) k₂) Ψ :=
  SPComp.bind_pure (SPComp.sample α) ▸ rHoare_bij_step f h

/-- Combined same-distribution coupling step.

Combines `rHoare_bind` + `rHoare_sample_same` in one step.
When both sides sample from the same distribution, this reduces to proving
the continuation for each sampled value `a` shared by both sides.

Replaces the common pattern:
```
apply liftR_bind liftR_uniform_same
intro a a' haa'; subst haa'
```
with a single application. -/
theorem rHoare_same_step {α γ δ : Type*} {Φ : RPre} {Ψ : RPost γ δ}
    [Fintype α] [Nonempty α]
    {k₁ : α → SPComp γ} {k₂ : α → SPComp δ}
    (h : ∀ a, rHoare Φ (k₁ a) (k₂ a) Ψ) :
    rHoare Φ (SPComp.bind (SPComp.sample α) k₁) (SPComp.bind (SPComp.sample α) k₂) Ψ := by
  intro h₁ h₂ hΦ
  simp only [SPComp.bind, SPComp.sample, SDistr.bind_assoc, SDistr.pure_bind]
  apply liftR_bind liftR_uniform_same
  intro a a' haa'
  subst haa'
  exact h a h₁ h₂ hΦ

/-! ## Canonicalization Lemmas

These lemmas help put SPComp programs into a canonical form for
easier comparison and simplification.
-/

/-- Bind of bind can be reassociated (left-to-right). -/
theorem bind_assoc_lr {α β γ : Type}
    (c : SPComp α) (f : α → SPComp β) (g : β → SPComp γ) :
    (c.bind f).bind g = c.bind (fun a => (f a).bind g) :=
  SPComp.bind_assoc c f g

/-- Pure on the left of bind simplifies. -/
theorem pure_bind_lr {α β : Type} (a : α) (f : α → SPComp β) :
    (pure a : SPComp α).bind f = f a :=
  SPComp.pure_bind a f

/-- Bind with pure on the right is identity. -/
theorem bind_pure_lr {α : Type} (c : SPComp α) :
    c.bind pure = c :=
  SPComp.bind_pure c

/-! ## FoldM Rule -/

/-- Relational Hoare rule for foldM: if each step preserves the invariant,
    then foldM preserves it.

    `Inv a₁ a₂` is the loop invariant parameterized by the accumulators on both sides.
    The precondition establishes `Inv a₁ a₂`, and each step must preserve it. -/
theorem rHoare_foldM {Inv : α → α → RPre}
    (steps₁ steps₂ : List (α → SPComp α))
    (h_len : steps₁.length = steps₂.length)
    (h_step : ∀ i (hi : i < steps₁.length) a₁ a₂,
      rHoare (Inv a₁ a₂) (steps₁[i] a₁) (steps₂[i] a₂)
        (fun b₁ h₁ b₂ h₂ => Inv b₁ b₂ h₁ h₂))
    (a₁ a₂ : α)  :
    rHoare (Inv a₁ a₂) (SPComp.foldM a₁ steps₁) (SPComp.foldM a₂ steps₂)
      (fun b₁ h₁ b₂ h₂ => Inv b₁ b₂ h₁ h₂) := by
  induction steps₁ generalizing steps₂ a₁ a₂ with
  | nil =>
    cases steps₂ with
    | nil =>
      simp only [SPComp.foldM]
      exact rHoare_ret (fun _ _ h => h)
    | cons => simp at h_len
  | cons f₁ rest₁ ih =>
    cases steps₂ with
    | nil => simp at h_len
    | cons f₂ rest₂ =>
      simp only [SPComp.foldM_cons]
      show rHoare (Inv a₁ a₂) (SPComp.bind (f₁ a₁) (fun a => SPComp.foldM a rest₁))
           (SPComp.bind (f₂ a₂) (fun a => SPComp.foldM a rest₂))
           (fun b₁ h₁ b₂ h₂ => Inv b₁ b₂ h₁ h₂)
      apply rHoare_bind (Ψ := fun b₁ h₁ b₂ h₂ => Inv b₁ b₂ h₁ h₂)
      · exact h_step 0 (Nat.zero_lt_succ _) a₁ a₂
      · intro b₁ b₂
        apply ih rest₂ (by simpa using h_len)
          (fun i hi => h_step (i + 1) (Nat.succ_lt_succ hi))

end CatCrypt.Relational
