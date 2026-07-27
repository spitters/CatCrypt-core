/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.NonUniform.Sample

/-!
# Independent products of sub-distributions

`prod d₁ d₂` is the distribution of an independent pair: sample `d₁`, sample `d₂`,
return both. `piFin ds` is the finite indexed product — one independent draw per
index of `Fin n`, returned as a function.

## Main definitions

* `prod d₁ d₂` — the independent product of two sub-distributions
* `piFin ds` — the independent product of a `Fin n`-indexed family
* `replicateFin n d` — `piFin` of the constant family, `n` independent draws from
  one sub-distribution

## Main results

* `mass_bind_of_mass_one` — a bind of total distributions is total
* `mass_prod`, `mass_piFin`, `mass_replicateFin` — a product of total
  distributions is total
* `prod_bind_fst`, `prod_bind_snd` — the two marginals of a product, when the
  discarded factor is total

## Correspondence with EasyCrypt

`prod` is the image of EasyCrypt's ``(`*`)`` of the `Distr` theory, whose
definition `dprod_dlet` gives as `dlet da (fun a => dmap db (fun b => (a, b)))` —
the bind form `prod` is defined by.
-/

set_option autoImplicit false

namespace CatCrypt.NonUniform

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

variable {α β : Type*}

/-! ## Mass of a bind -/

/-- Bind of total distributions is total. Obtained from `Unary.lossless_bind`
through `sampleFrom`, whose mass is the mass of its distribution. -/
theorem mass_bind_of_mass_one {d : SDistr α} {f : α → SDistr β}
    (hd : SDistr.mass d = 1) (hf : ∀ a, SDistr.mass (f a) = 1) :
    SDistr.mass (d.bind f) = 1 := by
  rw [← isLossless_sampleFrom_iff, ← sampleFrom_bind_sampleFrom]
  exact Unary.lossless_bind ((isLossless_sampleFrom_iff d).mpr hd)
    fun a => (isLossless_sampleFrom_iff (f a)).mpr (hf a)

/-! ## The binary product -/

/-- The independent product of two sub-distributions: a pair whose components are
drawn from `d₁` and `d₂`. -/
noncomputable def prod (d₁ : SDistr α) (d₂ : SDistr β) : SDistr (α × β) :=
  d₁.bind fun a => d₂.bind fun b => SDistr.pure (a, b)

/-- The product is the two binds its definition is. -/
theorem prod_eq_bind (d₁ : SDistr α) (d₂ : SDistr β) :
    prod d₁ d₂ = d₁.bind fun a => d₂.bind fun b => SDistr.pure (a, b) := rfl

/-- A product of total distributions is total. -/
theorem mass_prod {d₁ : SDistr α} {d₂ : SDistr β}
    (h₁ : SDistr.mass d₁ = 1) (h₂ : SDistr.mass d₂ = 1) :
    SDistr.mass (prod d₁ d₂) = 1 :=
  mass_bind_of_mass_one h₁ fun _ =>
    mass_bind_of_mass_one h₂ fun _ => SDistr.mass_pure _

/-- The first marginal of a product is the first factor, when the second factor is
total. -/
theorem prod_bind_fst {d₁ : SDistr α} {d₂ : SDistr β} (h₂ : SDistr.mass d₂ = 1) :
    (prod d₁ d₂).bind (fun p => SDistr.pure p.1) = d₁ := by
  have h : ∀ a : α,
      (d₂.bind fun b => SDistr.pure (a, b)).bind (fun p => SDistr.pure p.1)
        = SDistr.pure a := fun a => by
    rw [SDistr.bind_assoc]
    simp only [SDistr.pure_bind]
    exact bind_const_of_mass_one h₂ (SDistr.pure a)
  rw [prod, SDistr.bind_assoc]
  simp only [h]
  exact SDistr.bind_pure d₁

/-- The second marginal of a product is the second factor, when the first factor
is total. -/
theorem prod_bind_snd {d₁ : SDistr α} {d₂ : SDistr β} (h₁ : SDistr.mass d₁ = 1) :
    (prod d₁ d₂).bind (fun p => SDistr.pure p.2) = d₂ := by
  have h : ∀ a : α,
      (d₂.bind fun b => SDistr.pure (a, b)).bind (fun p => SDistr.pure p.2) = d₂ := fun a => by
    rw [SDistr.bind_assoc]
    simp only [SDistr.pure_bind]
    exact SDistr.bind_pure d₂
  rw [prod, SDistr.bind_assoc]
  simp only [h]
  exact bind_const_of_mass_one h₁ d₂

/-! ## The finite indexed product -/

/-- The independent product of a `Fin n`-indexed family: one draw per index,
returned as a function. -/
noncomputable def piFin : {n : ℕ} → (Fin n → SDistr α) → SDistr (Fin n → α)
  | 0, _ => SDistr.pure (fun i => i.elim0)
  | _ + 1, ds =>
      (ds 0).bind fun a =>
        (piFin fun i => ds i.succ).bind fun f => SDistr.pure (Fin.cons a f)

@[simp] theorem piFin_zero (ds : Fin 0 → SDistr α) :
    piFin ds = SDistr.pure (fun i => i.elim0) := rfl

@[simp] theorem piFin_succ {n : ℕ} (ds : Fin (n + 1) → SDistr α) :
    piFin ds =
      (ds 0).bind fun a =>
        (piFin fun i => ds i.succ).bind fun f => SDistr.pure (Fin.cons a f) := rfl

/-- An indexed product of total distributions is total. -/
theorem mass_piFin : ∀ {n : ℕ} {ds : Fin n → SDistr α},
    (∀ i, SDistr.mass (ds i) = 1) → SDistr.mass (piFin ds) = 1
  | 0, _, _ => SDistr.mass_pure _
  | _ + 1, _, h =>
      mass_bind_of_mass_one (h 0) fun _ =>
        mass_bind_of_mass_one (mass_piFin fun i => h i.succ) fun _ => SDistr.mass_pure _

/-- `n` independent draws from one sub-distribution. -/
noncomputable def replicateFin (n : ℕ) (d : SDistr α) : SDistr (Fin n → α) :=
  piFin fun _ => d

/-- Repeated independent draws from a total distribution are total. -/
theorem mass_replicateFin {n : ℕ} {d : SDistr α} (h : SDistr.mass d = 1) :
    SDistr.mass (replicateFin n d) = 1 :=
  mass_piFin fun _ => h

end CatCrypt.NonUniform
