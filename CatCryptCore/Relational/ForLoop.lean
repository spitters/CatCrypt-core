/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Relational.Rules

/-!
# pRHL Loop-Congruence Rules

Relational Hoare rules for `List.forM` and `List.foldlM` over `SPComp`,
analogous to VCVio's `rvcstep` congruence steps for `List.mapM`/`List.foldlM`.

Instead of manually unrolling lists with repeated `rHoare_bind`/`rHoare_ret`,
these rules discharge a synchronized loop in one application:

* `rHoare_forM` — the two sides iterate over lists `xs`, `ys` related pointwise
  by `R` (a `List.Forall₂ R xs ys` witness); a heap invariant `I : RPre` is
  carried through every iteration.
* `rHoare_forM_same` — the common synchronous specialization: same input list,
  two different loop bodies related pointwise.
* `rHoare_foldlM` — like `rHoare_forM`, but `List.foldlM` additionally threads
  accumulators; a value relation `V` on the accumulators is carried alongside
  the heap invariant `I`.
* `rHoare_foldlM_same` — synchronous `foldlM` specialization (same list, same
  accumulator relation, bodies related pointwise).

A unary companion section (in the `CatCrypt.Core.SPComp` namespace) provides
the `IsPure` loop lemmas:

* `SPComp.mapM_isPure` / `SPComp.forM_isPure` / `SPComp.foldlM_isPure` — a
  monadic loop whose body is heap-pure at every element of the list is
  heap-pure. These discharge the `IsPure` side conditions on games defined
  via `List.mapM` (e.g. Helios `privacy_real`/`privacy_ideal`).

## Usage sketch

```
-- Both sides write the same key schedule; heap equality is invariant:
example (l : Location) (vs : List l.ty) :
    rHoare eqPre (vs.forM fun v => SPComp.set l v)
                 (vs.forM fun v => SPComp.set l v)
      (fun _ h₁ _ h₂ => eqPre h₁ h₂) :=
  rHoare_forM_same vs fun v _ => rHoare_set_sync l v ...
```
-/

set_option autoImplicit false

namespace CatCrypt.Core.SPComp

universe u' v' w'

variable {α : Type u'} {β : Type v'}

/-! ## Unary `IsPure` loop lemmas -/

/-- `List.mapM` over `SPComp` is heap-pure when the body is heap-pure at every
element of the list. -/
theorem mapM_isPure {f : α → SPComp β} {xs : List α}
    (h : ∀ x ∈ xs, IsPure (f x)) : IsPure (xs.mapM f) := by
  induction xs with
  | nil => exact pure_isPure _
  | cons x xs ih =>
    rw [List.mapM_cons]
    exact bind_isPure (h x (List.mem_cons_self ..)) fun b =>
      bind_isPure (ih fun y hy => h y (List.mem_cons_of_mem _ hy)) fun _ =>
        pure_isPure _

/-- `List.forM` over `SPComp` is heap-pure when the body is heap-pure at every
element of the list. -/
theorem forM_isPure {f : α → SPComp PUnit} {xs : List α}
    (h : ∀ x ∈ xs, IsPure (f x)) : IsPure (xs.forM f) := by
  induction xs with
  | nil => exact pure_isPure _
  | cons x xs ih =>
    exact bind_isPure (h x (List.mem_cons_self ..)) fun _ =>
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- `List.foldlM` over `SPComp` is heap-pure when the step is heap-pure at
every accumulator and every element of the list. -/
theorem foldlM_isPure {σ : Type w'} {f : σ → α → SPComp σ} {xs : List α}
    (h : ∀ s, ∀ x ∈ xs, IsPure (f s x)) {s : σ} :
    IsPure (xs.foldlM f s) := by
  induction xs generalizing s with
  | nil => exact pure_isPure _
  | cons x xs ih =>
    rw [List.foldlM_cons]
    exact bind_isPure (h s x (List.mem_cons_self ..)) fun t =>
      ih fun s' y hy => h s' y (List.mem_cons_of_mem _ hy)

end CatCrypt.Core.SPComp

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

universe u v w x

variable {α : Type u} {β : Type v}

/-! ## `List.forM` congruence -/

/-- Loop congruence for `List.forM`: if `xs` and `ys` are related pointwise by
`R` and every related pair of loop bodies preserves the heap invariant `I`,
then the two loops preserve `I`. -/
theorem rHoare_forM {R : α → β → Prop} {I : RPre}
    {f : α → SPComp PUnit} {g : β → SPComp PUnit}
    {xs : List α} {ys : List β}
    (hR : List.Forall₂ R xs ys)
    (hbody : ∀ x y, R x y → rHoare I (f x) (g y) (fun _ h₁ _ h₂ => I h₁ h₂)) :
    rHoare I (xs.forM f) (ys.forM g) (fun _ h₁ _ h₂ => I h₁ h₂) := by
  induction hR with
  | nil => exact rHoare_ret fun _ _ h => h
  | cons hxy _ ih =>
    -- `(x :: xs).forM f` is definitionally `f x >>= fun _ => xs.forM f`
    exact rHoare_bind (hbody _ _ hxy) fun _ _ => ih

/-- Synchronous specialization of `rHoare_forM`: both sides iterate over the
same list `xs`, with loop bodies `f` and `g` related pointwise on the elements
of `xs`. -/
theorem rHoare_forM_same {I : RPre}
    {f g : α → SPComp PUnit} (xs : List α)
    (hbody : ∀ x ∈ xs, rHoare I (f x) (g x) (fun _ h₁ _ h₂ => I h₁ h₂)) :
    rHoare I (xs.forM f) (xs.forM g) (fun _ h₁ _ h₂ => I h₁ h₂) := by
  refine rHoare_forM (R := fun x y => x = y ∧ x ∈ xs)
    (List.forall₂_same.mpr fun x hx => ⟨rfl, hx⟩) ?_
  rintro x y ⟨rfl, hx⟩
  exact hbody x hx

/-! ## `List.foldlM` congruence -/

/-- Loop congruence for `List.foldlM`: in addition to the heap invariant `I`,
a value relation `V` on the accumulators is threaded through every iteration.
If the initial accumulators are `V`-related and each related step preserves
both `I` and `V`, the folds end `I`-and-`V`-related. -/
theorem rHoare_foldlM {σ₁ : Type w} {σ₂ : Type x}
    {R : α → β → Prop} {V : σ₁ → σ₂ → Prop} {I : RPre}
    {f : σ₁ → α → SPComp σ₁} {g : σ₂ → β → SPComp σ₂}
    {xs : List α} {ys : List β}
    (hR : List.Forall₂ R xs ys)
    (hbody : ∀ s₁ s₂ x y, R x y → V s₁ s₂ →
      rHoare I (f s₁ x) (g s₂ y) (fun t₁ h₁ t₂ h₂ => I h₁ h₂ ∧ V t₁ t₂))
    {s₁ : σ₁} {s₂ : σ₂} (hV : V s₁ s₂) :
    rHoare I (xs.foldlM f s₁) (ys.foldlM g s₂)
      (fun t₁ h₁ t₂ h₂ => I h₁ h₂ ∧ V t₁ t₂) := by
  induction hR generalizing s₁ s₂ with
  | nil => exact rHoare_ret fun _ _ h => ⟨h, hV⟩
  | cons hxy _ ih =>
    simp only [List.foldlM_cons]
    refine rHoare_bind (hbody _ _ _ _ hxy hV) fun t₁ t₂ => ?_
    exact fun h₁ h₂ hpre => ih hpre.2 h₁ h₂ hpre.1

/-- Synchronous specialization of `rHoare_foldlM`: both sides fold over the
same list `xs`, with step functions related pointwise on elements of `xs`. -/
theorem rHoare_foldlM_same {σ₁ : Type w} {σ₂ : Type x}
    {V : σ₁ → σ₂ → Prop} {I : RPre}
    {f : σ₁ → α → SPComp σ₁} {g : σ₂ → α → SPComp σ₂}
    (xs : List α)
    (hbody : ∀ s₁ s₂, ∀ x ∈ xs, V s₁ s₂ →
      rHoare I (f s₁ x) (g s₂ x) (fun t₁ h₁ t₂ h₂ => I h₁ h₂ ∧ V t₁ t₂))
    {s₁ : σ₁} {s₂ : σ₂} (hV : V s₁ s₂) :
    rHoare I (xs.foldlM f s₁) (xs.foldlM g s₂)
      (fun t₁ h₁ t₂ h₂ => I h₁ h₂ ∧ V t₁ t₂) := by
  refine rHoare_foldlM (R := fun x y => x = y ∧ x ∈ xs)
    (List.forall₂_same.mpr fun x hx => ⟨rfl, hx⟩) ?_ hV
  rintro s₁' s₂' x y ⟨rfl, hx⟩ hV'
  exact hbody s₁' s₂' x hx hV'

/-! ## Examples -/

/-- Writing the same value sequence to a location on both sides preserves heap
equality, in one rule application — no manual unrolling. -/
example (l : Location) (vs : List l.ty) :
    rHoare eqPre (vs.forM fun v => SPComp.set l v)
                 (vs.forM fun v => SPComp.set l v)
      (fun _ h₁ _ h₂ => eqPre h₁ h₂) :=
  rHoare_forM_same vs fun v _ =>
    rHoare_set_sync l v fun _ _ h => by
      simp only [eqPre] at h ⊢; rw [h]

/-- Folding the same pure accumulation over equal heaps keeps the accumulators
equal: `V` is equality on the accumulator, `I` is heap equality. -/
example (xs : List ℕ) :
    rHoare eqPre
      (xs.foldlM (fun s x => (pure (s + x) : SPComp ℕ)) 0)
      (xs.foldlM (fun s x => (pure (s + x) : SPComp ℕ)) 0)
      (fun s₁ h₁ s₂ h₂ => eqPre h₁ h₂ ∧ s₁ = s₂) :=
  rHoare_foldlM_same (V := fun (s₁ s₂ : ℕ) => s₁ = s₂) xs
    (fun s₁ s₂ x _ hV => rHoare_ret fun _ _ h => ⟨h, by rw [hV]⟩)
    rfl

end CatCrypt.Relational
