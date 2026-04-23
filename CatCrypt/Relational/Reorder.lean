/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Relational.Rules

/-!
# Seq-Swap / Reorder Rules

Relational rules for commuting operations without syntactically rewriting programs.
These are the CatCrypt analogue of Bluebell's `seq-swap` rule: when the head
operations on two sides of a pRHL judgment don't match, we commute pure or
independent operations past each other to bring them into alignment.

## Main theorems

* `rHoare_reorder_pure_l` — commute an `IsPure` computation past anything on LHS
* `rHoare_reorder_pure_r` — symmetric variant for RHS
* `rHoare_sample_comm` — both sides sample α,β but in opposite order
* `rHoare_sample_past_get_l` — commute sample past get on LHS
* `rHoare_sample_past_set_l` — commute sample past set on LHS

## References

* Bluebell (POPL 2025) — `seq-swap` rule for randomness alignment
-/

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

variable {α β γ δ : Type}

/-! ## Pure reordering -/

/-- Reorder LHS: commute an `IsPure` computation past any other computation.

    If `c` is pure (heap-independent), then `c >>= fun x => d >>= fun y => k x y`
    is equivalent to `d >>= fun y => c >>= fun x => k x y`.
    We use this to align heads when the LHS starts with a pure operation
    but the RHS starts with something else. -/
theorem rHoare_reorder_pure_l {c : SPComp α} {d : SPComp β}
    {k : α → β → SPComp γ} {c₂ : SPComp δ} {Φ : RPre} {Ψ : RPost γ δ}
    (hPure : SPComp.IsPure c)
    (h : rHoare Φ (SPComp.bind d (fun y => SPComp.bind c (fun x => k x y))) c₂ Ψ) :
    rHoare Φ (SPComp.bind c (fun x => SPComp.bind d (fun y => k x y))) c₂ Ψ := by
  apply rHoare_swap_lhs _ h
  intro h₁
  exact congrFun (SPComp.isPure_bind_comm_left c d k hPure) h₁

/-- Reorder RHS: symmetric variant for the right-hand side. -/
theorem rHoare_reorder_pure_r {c₁ : SPComp γ} {c : SPComp α} {d : SPComp β}
    {k : α → β → SPComp δ} {Φ : RPre} {Ψ : RPost γ δ}
    (hPure : SPComp.IsPure c)
    (h : rHoare Φ c₁ (SPComp.bind d (fun y => SPComp.bind c (fun x => k x y))) Ψ) :
    rHoare Φ c₁ (SPComp.bind c (fun x => SPComp.bind d (fun y => k x y))) Ψ := by
  apply rHoare_swap_rhs _ h
  intro h₁
  exact congrFun (SPComp.isPure_bind_comm_left c d k hPure) h₁

/-! ## Advantage-level reordering -/

open CatCrypt.Crypto

/-- Factor out a common `IsPure` prefix from two games.

    If both games have the form `pfx.bind(p => Gᵢ.bind(r => k p r))`,
    where `pfx` is `IsPure`, then we can commute `pfx` past `Gᵢ` and factor:

    `AdvantageA (pfx.bind(p => G₁.bind(r => k p r)))
               (pfx.bind(p => G₂.bind(r => k p r))) A
     = AdvantageA G₁ G₂ (fun r => pfx.bind(p => (k p r).bind A))`

    This combines `isPure_bind_comm` + `advantage_factorization` into a single step,
    which is the key pattern in the Double Ratchet inductive step. -/
theorem advantage_factorization_comm {α β γ : Type}
    (pfx : SPComp α) (G₁ G₂ : SPComp β) (k : α → β → SPComp γ)
    (hPure : SPComp.IsPure pfx)
    (A : γ → SPComp Bool) :
    AdvantageA (pfx.bind (fun p => G₁.bind (fun r => k p r)))
               (pfx.bind (fun p => G₂.bind (fun r => k p r))) A =
    AdvantageA G₁ G₂ (fun r => pfx.bind (fun p => (k p r).bind A)) := by
  -- Step 1: commute prefix past G₁ and G₂ using isPure_bind_comm_left
  have comm₁ : pfx.bind (fun p => G₁.bind (fun r => k p r)) =
      G₁.bind (fun r => pfx.bind (fun p => k p r)) :=
    SPComp.isPure_bind_comm_left pfx G₁ k hPure
  have comm₂ : pfx.bind (fun p => G₂.bind (fun r => k p r)) =
      G₂.bind (fun r => pfx.bind (fun p => k p r)) :=
    SPComp.isPure_bind_comm_left pfx G₂ k hPure
  rw [comm₁, comm₂]
  -- Step 2: factor out the common suffix
  rw [advantage_factorization (fun r => pfx.bind (fun p => k p r)) G₁ G₂ A]
  -- Step 3: reassociate: (pfx.bind(p => k p r)).bind A = pfx.bind(p => (k p r).bind A)
  congr 1; funext r
  exact SPComp.bind_assoc pfx (fun p => k p r) A

/-! ## Sample commutativity -/

/-- Both sides sample α,β but in opposite order: align them.

    If the LHS samples `α` then `β`, and the RHS samples `β` then `α`,
    we can swap the RHS to match. -/
theorem rHoare_sample_comm [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    {k₁ k₂ : α → β → SPComp γ} {Φ : RPre} {Ψ : RPost γ γ}
    (h : ∀ a b, rHoare Φ (k₁ a b) (k₂ a b) Ψ) :
    rHoare Φ
      (SPComp.bind (SPComp.sample α) (fun x => SPComp.bind (SPComp.sample β) (fun y => k₁ x y)))
      (SPComp.bind (SPComp.sample β) (fun y => SPComp.bind (SPComp.sample α) (fun x => k₂ x y)))
      Ψ := by
  -- Swap the RHS to α-then-β order
  have heq : ∀ h₁ : Heap,
      (SPComp.bind (SPComp.sample β) (fun y => SPComp.bind (SPComp.sample α) (fun x => k₂ x y))) h₁ =
      (SPComp.bind (SPComp.sample α) (fun x => SPComp.bind (SPComp.sample β) (fun y => k₂ x y))) h₁ :=
    fun h₁ => SPComp.swap_sample_sample β α γ (fun b a => k₂ a b) h₁
  apply rHoare_swap_rhs heq
  -- Now both sides sample α then β
  intro h₁ h₂ hΦ
  simp only [SPComp.bind_def, SPComp.sample]
  rw [SDistr.bind_assoc, SDistr.bind_assoc]
  conv_lhs => arg 2; ext a; rw [SDistr.pure_bind, SDistr.bind_assoc]; arg 2; ext b; rw [SDistr.pure_bind]
  conv_rhs => arg 2; ext a; rw [SDistr.pure_bind, SDistr.bind_assoc]; arg 2; ext b; rw [SDistr.pure_bind]
  apply liftR_bind liftR_uniform_same
  intro a a' haa'; subst haa'
  apply liftR_bind liftR_uniform_same
  intro b b' hbb'; subst hbb'
  exact h a b h₁ h₂ hΦ

/-! ## Sample past get/set -/

/-- Commute sample past get on the LHS.

    `sample α >>= fun x => get l >>= fun v => k x v` is equivalent to
    `get l >>= fun v => sample α >>= fun x => k x v` because
    sample doesn't read the heap and get doesn't modify the distribution. -/
theorem rHoare_sample_past_get_l [Fintype α] [Nonempty α]
    {l : Location} {k : α → l.ty → SPComp β} {c₂ : SPComp δ}
    {Φ : RPre} {Ψ : RPost β δ}
    (h : rHoare Φ
      (SPComp.bind (SPComp.get l) (fun v => SPComp.bind (SPComp.sample α) (fun x => k x v)))
      c₂ Ψ) :
    rHoare Φ
      (SPComp.bind (SPComp.sample α) (fun x => SPComp.bind (SPComp.get l) (fun v => k x v)))
      c₂ Ψ := by
  apply rHoare_swap_lhs _ h
  intro h₁
  exact SPComp.swap_sample_get α β l k h₁

/-- Commute sample past set on the LHS.

    `sample α >>= fun x => set l v >> k x` is equivalent to
    `set l v >> sample α >>= fun x => k x` because
    sample is independent of the heap. -/
theorem rHoare_sample_past_set_l [Fintype α] [Nonempty α]
    {l : Location} {v : l.ty} {k : α → SPComp β} {c₂ : SPComp δ}
    {Φ : RPre} {Ψ : RPost β δ}
    (h : rHoare Φ
      (SPComp.bind (SPComp.set l v) (fun _ => SPComp.bind (SPComp.sample α) (fun x => k x)))
      c₂ Ψ) :
    rHoare Φ
      (SPComp.bind (SPComp.sample α) (fun x => SPComp.bind (SPComp.set l v) (fun _ => k x)))
      c₂ Ψ := by
  apply rHoare_swap_lhs _ h
  intro h₁
  exact SPComp.swap_sample_set α β l v k h₁

end CatCrypt.Relational
