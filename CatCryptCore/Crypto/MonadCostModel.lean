/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCryptCore.Crypto.UCAdmClass
public import CatCryptCore.Core.SPTree
public import CatCryptCore.Crypto.UCMonad.SPCompInstance

/-!
# Monad Cost Model and Query-Bounded Admissibility

This file defines `MonadCostModel`, a graded refinement of `UCAdmClass`, and
provides a concrete **query-bounded admissibility** class for `SPComp` via
`SPTree` syntax trees.

## The Classical Cost Insight

All quantum admissibility candidates (BQP, reactive poly-time, query complexity)
depend on a *classical* complexity measure of the program description. The cost
algebra `(ℕ∞, +, ≤)` is shared between `SPComp` and `QComp`. Only the cost
*function* differs — counting sample calls vs. instrument applications.

## Architecture

```
UCAdmClass T                     (abstract: adm predicate)
     ↑
MonadCostModel T                 (graded: cost : (α → T β) → ℕ∞)
     ↑
spTreeQueryAdm : UCAdmClass SPComp   (concrete: adm via SPTree witnesses)
```

`spTreeQueryAdm` is a **def** (not instance) to avoid diamond with the existing
trivial `UCAdmClass SPComp` instance. Use `letI := spTreeQueryAdm` locally.

## Main definitions

* `MonadCostModel` — assigns `ℕ∞` costs, subadditive under bind
* `UCAdmClass_of_costModel` — derives `UCAdmClass` with `adm f := cost f < ⊤`
* `spTreeQueryAdm` — concrete `UCAdmClass SPComp` via SPTree witnesses

## Main results

* `spTreeQueryAdm` is an admissibility class that some Kleisli arrows fail:
  an opaque function with no syntax-tree witness is outside it
-/

@[expose] public section

open scoped ENNReal

namespace UCMonad

/-! ## Section 1: Abstract Cost Model -/

/-- A cost model for a monad: assigns `ℕ∞`-valued costs to Kleisli arrows,
    subadditive under composition.

    The cost algebra `(ℕ∞, +, ≤)` is the same for both classical (`SPComp`)
    and quantum (`QComp d`) monads — only the cost function differs. -/
class MonadCostModel (T : Type → Type) [Monad T] [UCMonadBase T] where
  /-- Cost of a Kleisli arrow (worst-case over all inputs). -/
  cost : {α β : Type} → (α → T β) → WithTop ℕ
  /-- Pure (identity) has zero cost. -/
  cost_pure {α : Type} : cost (pure : α → T α) = 0
  /-- Cost is subadditive under Kleisli composition. -/
  cost_bind {α β γ : Type} {f : α → T β} {g : β → T γ} :
    cost (fun a => f a >>= g) ≤ cost f + cost g
  /-- Coproduct doesn't exceed maximum component cost. -/
  cost_mapSum {α β γ δ : Type} {f : α → T β} {g : γ → T δ} :
    cost (UCMonadBase.ucMapSum f g) ≤ max (cost f) (cost g)
  /-- Precomposing with a pure function doesn't increase cost. -/
  cost_precomp {α α' β : Type} {g : α → T β} (f : α' → α) :
    cost (g ∘ f) ≤ cost g

export MonadCostModel (cost cost_pure cost_bind cost_mapSum cost_precomp)

/-! ## Section 2: UCAdmClass from Cost Model -/

/-- Derive `UCAdmClass` from a cost model: `adm f := cost f < ⊤`.

    "Admissible" = "has finite worst-case cost". Closure:
    - `pure`: cost 0 < ⊤ ✓
    - `bind`: finite + finite < ⊤ ✓
    - `mapSum`: max(finite, finite) < ⊤ ✓

    This is a `def`, not an `instance`, to avoid diamonds with existing
    trivial instances. Use `letI := UCAdmClass_of_costModel T` locally. -/
noncomputable def UCAdmClass_of_costModel
    (T : Type → Type) [Monad T] [UCMonadBase T] [MonadCostModel T] :
    UCAdmClass T where
  adm f := cost f < ⊤
  adm_pure {α} := by rw [cost_pure]; exact WithTop.top_pos
  adm_bind hf hg := lt_of_le_of_lt cost_bind (WithTop.add_lt_top.mpr ⟨hf, hg⟩)
  adm_mapSum hf hg := by
    apply lt_of_le_of_lt
    · exact cost_mapSum
    · exact max_lt hf hg
  adm_precomp f hg := lt_of_le_of_lt (cost_precomp f) hg

/-! ## Section 3: Graded Subcategories -/

section GradedSubcategories

variable {T : Type → Type} [Monad T] [UCMonadBase T] [MonadCostModel T]

/-- A Kleisli arrow has cost bounded by `n`.

    The family `costBounded n` for `n : ℕ` gives a filtered system of
    wide subcategories of Kl(T):
    ```
      costBounded 0 ⊂ costBounded 1 ⊂ ... ⊂ costBounded n ⊂ ... ⊂ adm
    ```
    where `adm = ⋃ₙ costBounded n = {f | cost f < ⊤}`.

    This connects to Katsumata's graded monad framework: `cost` is a lax
    monoidal functor from (Kl(T), >>=, pure) to (ℕ∞, +, 0, ≤). -/
def costBounded (n : ℕ) {α β : Type} (f : α → T β) : Prop :=
  cost f ≤ n

/-- Pure has cost 0: identity morphisms are in the 0-graded subcategory. -/
theorem costBounded_pure {α : Type} : costBounded (T := T) 0 (pure : α → T α) := by
  simp [costBounded, cost_pure]

/-- Kleisli composition respects the grading: costs add. -/
theorem costBounded_bind {α β γ : Type} {f : α → T β} {g : β → T γ} {n m : ℕ}
    (hf : costBounded n f) (hg : costBounded m g) :
    costBounded (n + m) (fun a => f a >>= g) := by
  unfold costBounded at *
  calc cost (fun a => f a >>= g) ≤ cost f + cost g := cost_bind
    _ ≤ ↑n + ↑m := add_le_add hf hg
    _ = ↑(n + m) := by push_cast; ring

/-- Coproduct respects the grading: cost is max of components. -/
theorem costBounded_mapSum {α β γ δ : Type} {f : α → T β} {g : γ → T δ} {n m : ℕ}
    (hf : costBounded n f) (hg : costBounded m g) :
    costBounded (max n m) (UCMonadBase.ucMapSum f g) := by
  unfold costBounded at *
  calc cost (UCMonadBase.ucMapSum f g) ≤ max (cost f) (cost g) := cost_mapSum
    _ ≤ max (↑n) (↑m) := max_le_max hf hg
    _ = ↑(max n m) := by norm_cast

/-- Monotonicity: smaller cost bound implies larger cost bound. -/
theorem costBounded_mono {α β : Type} {f : α → T β} {n m : ℕ} (hnm : n ≤ m)
    (h : costBounded n f) : costBounded m f := by
  unfold costBounded at *
  exact le_trans h (WithTop.coe_le_coe.mpr hnm)

/-- Cost-bounded implies admissible (via `UCAdmClass_of_costModel`).

    Every `costBounded n f` arrow is admissible in the cost-derived `UCAdmClass`.
    This is the inclusion `⋃ₙ costBounded n ⊆ adm`. -/
theorem adm_of_costBounded {α β : Type} {f : α → T β} {n : ℕ}
    (h : costBounded n f) :
    (UCAdmClass_of_costModel T).adm f := by
  show cost f < ⊤
  exact lt_of_le_of_lt h (WithTop.coe_lt_top n)

end GradedSubcategories

/-! ## Section 4: SPComp Query-Bounded Admissibility via SPTree -/

open CatCrypt.Core CatCrypt.Crypto

/-- A Kleisli arrow `f : α → SPComp β` is **query-bounded** if there exists
    a syntax tree representation with uniformly bounded operation count.

    Membership in the class:
    - Opaque functions without syntax tree witnesses are NOT admissible
    - All programs built from standard SPComp constructors ARE admissible
    - The class is closed under bind (splicing trees) and mapSum (case analysis) -/
noncomputable def spTreeQueryAdm : UCAdmClass SPComp where
  adm {α β} f :=
    ∃ (s : α → SPTree β),
      (∀ a, (s a).compile = f a) ∧
      ∃ n, ∀ a, (s a).queryCost ≤ n
  adm_pure :=
    ⟨SPTree.ret, fun _ => rfl, 0, fun _ => le_refl 0⟩
  adm_bind {α β γ} {f g} hf hg := by
    obtain ⟨sf, hsf, nf, hcf⟩ := hf
    obtain ⟨sg, hsg, ng, hcg⟩ := hg
    refine ⟨fun a => (sf a).bind sg, ?_, nf + ng, ?_⟩
    · intro a
      rw [SPTree.compile_bind, hsf a]
      congr 1; funext b; exact hsg b
    · intro a
      exact le_trans
        (SPTree.queryCost_bind (sf a) sg ng hcg)
        (Nat.add_le_add_right (hcf a) ng)
  adm_mapSum {α β γ δ} {f g} hf hg := by
    obtain ⟨sf, hsf, nf, hcf⟩ := hf
    obtain ⟨sg, hsg, ng, hcg⟩ := hg
    refine ⟨fun x => match x with
      | .inl a => (sf a).bind (fun b => SPTree.ret (.inl b))
      | .inr c => (sg c).bind (fun b => SPTree.ret (.inr b)), ?_, max nf ng, ?_⟩
    · intro x; cases x with
      | inl a =>
        simp only [SPTree.compile_bind, SPTree.compile_ret, hsf]
        show SPComp.bind (f a) (fun b => SPComp.pure (Sum.inl b)) =
          UCMonadBase.ucMapSum f g (.inl a)
        simp [UCMonadBase.ucMapSum, mapSumSP, SPComp.map]
      | inr c =>
        simp only [SPTree.compile_bind, SPTree.compile_ret, hsg]
        show SPComp.bind (g c) (fun b => SPComp.pure (Sum.inr b)) =
          UCMonadBase.ucMapSum f g (.inr c)
        simp [UCMonadBase.ucMapSum, mapSumSP, SPComp.map]
    · intro x; cases x with
      | inl a =>
        show ((sf a).bind (fun b => SPTree.ret (Sum.inl b))).queryCost ≤ max nf ng
        calc ((sf a).bind (fun b => SPTree.ret (Sum.inl b))).queryCost
            ≤ (sf a).queryCost + 0 :=
              SPTree.queryCost_bind _ _ 0 (fun _ => le_refl 0)
          _ = (sf a).queryCost := Nat.add_zero _
          _ ≤ nf := hcf a
          _ ≤ max nf ng := le_max_left _ _
      | inr c =>
        show ((sg c).bind (fun b => SPTree.ret (Sum.inr b))).queryCost ≤ max nf ng
        calc ((sg c).bind (fun b => SPTree.ret (Sum.inr b))).queryCost
            ≤ (sg c).queryCost + 0 :=
              SPTree.queryCost_bind _ _ 0 (fun _ => le_refl 0)
          _ = (sg c).queryCost := Nat.add_zero _
          _ ≤ ng := hcg c
          _ ≤ max nf ng := le_max_right _ _
  adm_precomp {α α' β} {g} f hg := by
    obtain ⟨sg, hsg, ng, hcg⟩ := hg
    exact ⟨sg ∘ f, fun a' => hsg (f a'), ng, fun a' => hcg (f a')⟩

end UCMonad
