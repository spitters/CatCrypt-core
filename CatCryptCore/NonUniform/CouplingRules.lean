/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.NonUniform.Sample
import CatCryptCore.Relational.Rules
import CatCryptCore.Relational.Sync

/-!
# pRHL sampling rules for arbitrary distributions

The `Prob/Coupling.lean` notion `liftR R d₁ d₂` — a joint sub-distribution with
marginals `d₁`, `d₂` whose support lies in `R` — is already stated for arbitrary
`SDistr`. The rules here consume such a coupling directly, so a pRHL sampling
step is available for any pair of distributions, not just uniform ones.

## Main results

* `rHoare_coupling_step` — the general two-sided sampling rule: a coupling of
  `d₁` and `d₂` plus the pointwise premise on the continuations gives
  `rHoare Φ (sampleFrom d₁ >>= k₁) (sampleFrom d₂ >>= k₂) Ψ`
* `rHoare_coupling` — bare form, no continuations
* `rHoare_bij_step_of_coupling`, `rHoare_same_step_of_coupling`,
  `rHoare_sample_vs_sample_coupling_of_coupling` — the uniform rules of
  `Relational/Rules.lean` and `Relational/Sync.lean` re-derived as instances,
  each with the statement of the existing rule verbatim
* `rHoare_sampleFrom_l`, `rHoare_sampleFrom_r` — one-sided rules, requiring the
  discarded distribution to be total
* `eq_of_rHoare_eqPost` — a full-equality judgment identifies the output
  sub-distributions
-/

namespace CatCrypt.NonUniform

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational

variable {α β γ δ : Type*}

/-! ## Pushforward couplings

`Prob/Coupling.lean` provides `liftR_uniform_bij`, which couples two uniform
distributions along a bijection. Bijectivity is used there only to identify the
pushforward of `SDistr.uniform α` with `SDistr.uniform β`; the coupling itself
exists for an arbitrary function and an arbitrary distribution. -/

/-- Graph coupling: an arbitrary function `f` couples `d` with its pushforward
    along `f`, the joint distribution being supported on the graph of `f`. -/
noncomputable def Coupling.graph (d : SDistr α) (f : α → β) :
    Prob.Coupling d (d.bind fun a => SDistr.pure (f a)) where
  joint := d.bind fun a => SDistr.pure (a, f a)
  left_marginal := fun _ => by
    simp only [SDistr.bind_assoc, SDistr.pure_bind, SDistr.bind_pure]
  right_marginal := fun _ => by
    simp only [SDistr.bind_assoc, SDistr.pure_bind]

/-- The graph coupling lifts the graph relation of `f`. -/
theorem liftR_graph (d : SDistr α) (f : α → β) :
    liftR (fun a b => f a = b) d (d.bind fun a => SDistr.pure (f a)) := by
  refine ⟨Coupling.graph d f, fun a b hab => ?_⟩
  simp only [Coupling.graph, SDistr.bind, PMF.bind_apply] at hab
  by_contra hne
  refine hab (ENNReal.tsum_eq_zero.mpr fun oa => ?_)
  cases oa with
  | none => simp [SDistr.fail, PMF.pure_apply]
  | some x =>
    simp only [SDistr.pure, PMF.pure_apply]
    have hneq : ¬(some (a, b) = some (x, f x)) := by
      simp only [Option.some.injEq, Prod.mk.injEq, not_and]
      exact fun hax hfab => hne (by rw [hax, hfab])
    rw [if_neg hneq, mul_zero]

/-- If the pushforward of `d` along `f` is `e`, then `f`'s graph relation lifts
    to `d` and `e`. -/
theorem liftR_pushforward {d : SDistr α} {e : SDistr β} {f : α → β}
    (h : (d.bind fun a => SDistr.pure (f a)) = e) :
    liftR (fun a b => f a = b) d e := h ▸ liftR_graph d f

/-- `Prob.liftR_uniform_bij` derived from `liftR_pushforward`: a bijection's only
    role is to make the pushforward of uniform uniform again. -/
theorem liftR_uniform_bij_of_pushforward [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α ≃ β) :
    (SDistr.uniform α) ⟨fun a b => f a = b⟩# (SDistr.uniform β) :=
  liftR_pushforward (SDistr.uniform_bind_bij f)

/-- The derived lemma and the library's `Prob.liftR_uniform_bij` are the same
    proposition. -/
example : @Prob.liftR_uniform_bij = @liftR_uniform_bij_of_pushforward := rfl

/-! ## The general two-sided rule -/

/--
Sampling rule for two arbitrary distributions related by a coupling.

Given a coupling of `d₁` and `d₂` supported in `R`, and continuations that are
related whenever their arguments are `R`-related, the two sampling programs are
related. Specialising `d₁ = d₂ = SDistr.uniform` and `R` to the graph of a
bijection recovers `rHoare_bij_step`; see `rHoare_bij_step_of_coupling`.
-/
theorem rHoare_coupling_step {Φ : RPre} {Ψ : RPost γ δ} {R : α → β → Prop}
    {d₁ : SDistr α} {d₂ : SDistr β} (hd : liftR R d₁ d₂)
    {k₁ : α → SPComp γ} {k₂ : β → SPComp δ}
    (hk : ∀ a b, R a b → rHoare Φ (k₁ a) (k₂ b) Ψ) :
    rHoare Φ (SPComp.bind (sampleFrom d₁) k₁) (SPComp.bind (sampleFrom d₂) k₂) Ψ :=
  fun h₁ h₂ hΦ => by
    rw [sampleFrom_bind_apply, sampleFrom_bind_apply]
    exact liftR_bind hd fun a b hab => hk a b hab h₁ h₂ hΦ

/-- Bare form of `rHoare_coupling_step`: the coupling relation appears in the
    postcondition alongside the preserved precondition. -/
theorem rHoare_coupling {Φ : RPre} {R : α → β → Prop}
    {d₁ : SDistr α} {d₂ : SDistr β} (hd : liftR R d₁ d₂) :
    rHoare Φ (sampleFrom d₁) (sampleFrom d₂)
      (fun a h₁ b h₂ => Φ h₁ h₂ ∧ R a b) :=
  fun h₁ h₂ hΦ => liftR_bind hd fun a b hab => liftR_pure ⟨hΦ, hab⟩

/-- Same distribution on both sides, diagonal coupling. -/
theorem rHoare_sampleFrom_same {Φ : RPre} {Ψ : RPost γ δ} (d : SDistr α)
    {k₁ : α → SPComp γ} {k₂ : α → SPComp δ}
    (hk : ∀ a, rHoare Φ (k₁ a) (k₂ a) Ψ) :
    rHoare Φ (SPComp.bind (sampleFrom d) k₁) (SPComp.bind (sampleFrom d) k₂) Ψ :=
  rHoare_coupling_step (liftR_refl d) fun a b hab => hab ▸ hk a

/-! ## The uniform rules as instances

Each rule below restates a uniform rule already in the library and proves it from
`rHoare_coupling_step`. The `example` after each one equates the two constants,
so the kernel checks that the restatement is the same proposition. -/

/-- `Relational.rHoare_bij_step` derived from `rHoare_coupling_step`.
    `SPComp.sample α` is `sampleFrom (SDistr.uniform α)` by definition, and
    `liftR_uniform_bij` supplies the coupling. -/
theorem rHoare_bij_step_of_coupling {α β γ δ : Type*} {Φ : RPre} {Ψ : RPost γ δ}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α ≃ β)
    {k₁ : α → SPComp γ} {k₂ : β → SPComp δ}
    (h : ∀ a, rHoare Φ (k₁ a) (k₂ (f a)) Ψ) :
    rHoare Φ (SPComp.bind (SPComp.sample α) k₁) (SPComp.bind (SPComp.sample β) k₂) Ψ :=
  rHoare_coupling_step (liftR_uniform_bij f) fun a b hab => hab ▸ h a

/-- The derived bijection rule and the library's `rHoare_bij_step` are the same
    proposition. -/
example : @Relational.rHoare_bij_step = @rHoare_bij_step_of_coupling := rfl

/-- `Relational.rHoare_same_step` derived from `rHoare_coupling_step`. -/
theorem rHoare_same_step_of_coupling {α γ δ : Type*} {Φ : RPre} {Ψ : RPost γ δ}
    [Fintype α] [Nonempty α]
    {k₁ : α → SPComp γ} {k₂ : α → SPComp δ}
    (h : ∀ a, rHoare Φ (k₁ a) (k₂ a) Ψ) :
    rHoare Φ (SPComp.bind (SPComp.sample α) k₁) (SPComp.bind (SPComp.sample α) k₂) Ψ :=
  rHoare_sampleFrom_same _ h

/-- The derived same-distribution rule and the library's `rHoare_same_step` are
    the same proposition. -/
example : @Relational.rHoare_same_step = @rHoare_same_step_of_coupling := rfl

/-- `Relational.r_sample_vs_sample_coupling` derived from `rHoare_coupling`.
    That rule takes a coupling of two *uniform* distributions; here the
    uniformity is only used to name the programs. -/
theorem r_sample_vs_sample_coupling_of_coupling {Φ : RPre} (α β : Type*)
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (R : α → β → Prop)
    (hCoupling : liftR R (SDistr.uniform α) (SDistr.uniform β)) :
    rHoare Φ (SPComp.sample α) (SPComp.sample β)
      (fun a h₁ b h₂ => Φ h₁ h₂ ∧ R a b) :=
  rHoare_coupling hCoupling

/-- The derived rule and the library's `r_sample_vs_sample_coupling` are the same
    proposition. -/
example : @Relational.r_sample_vs_sample_coupling = @r_sample_vs_sample_coupling_of_coupling :=
  rfl

/-! ## One-sided rules

A one-sided rule averages the other side over the sampled distribution, so the
sampled distribution must be total: if `SDistr.mass d < 1` the left program has
strictly smaller mass than the right and no coupling exists. -/

/-- One-sided sample on the left, for a total distribution. -/
theorem rHoare_sampleFrom_l {σ τ ρ : Type*} {Φ : RPre} {Ψ : RPost τ ρ}
    {d : SDistr σ} (hd : SDistr.mass d = 1)
    {c₂ : SPComp ρ} {f : σ → SPComp τ}
    (h : ∀ a, rHoare Φ (f a) c₂ Ψ) :
    rHoare Φ (SPComp.bind (sampleFrom d) f) c₂ Ψ := by
  intro h₁ h₂ hΦ
  rw [sampleFrom_bind_apply, ← bind_const_of_mass_one hd (c₂ h₂)]
  exact liftR_bind (R := Eq) (liftR_refl d) fun a _ _ => h a h₁ h₂ hΦ

/-- One-sided sample on the right, for a total distribution. -/
theorem rHoare_sampleFrom_r {σ τ ρ : Type*} {Φ : RPre} {Ψ : RPost ρ τ}
    {d : SDistr σ} (hd : SDistr.mass d = 1)
    {c₁ : SPComp ρ} {f : σ → SPComp τ}
    (h : ∀ a, rHoare Φ c₁ (f a) Ψ) :
    rHoare Φ c₁ (SPComp.bind (sampleFrom d) f) Ψ := by
  intro h₁ h₂ hΦ
  rw [sampleFrom_bind_apply, ← bind_const_of_mass_one hd (c₁ h₁)]
  exact liftR_bind (R := Eq) (liftR_refl d) fun _ a _ => h a h₁ h₂ hΦ

/-! ## From a full-equality judgment to distribution equality -/

/-- A judgment with `eqPre`/`eqPost` says the two programs have the same output
    sub-distribution from every heap: an equality coupling forces all mass onto
    the diagonal, and the two marginals then agree. -/
theorem eq_of_rHoare_eqPost {c₁ c₂ : SPComp α}
    (h : rHoare eqPre c₁ c₂ eqPost) (h₀ : Heap) : c₁ h₀ = c₂ h₀ :=
  liftR_eq_implies_eq (liftR_mono (fun _ _ hpost => Prod.ext hpost.1 hpost.2) (h h₀ h₀ rfl))

end CatCrypt.NonUniform
