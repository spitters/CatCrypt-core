/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.UC

/-!
# Robust Compilation (RC), RHP, and the UC = RC Equivalence

This file defines three notions of security preservation and establishes their
relationships at Level 1 (information-theoretic, no complexity bounds).

## Three notions of robust compilation

1. **`RobustCompilation`** (our notion, no simulator):
   `∀ ρ D, sdist(D∘ρ∘π, D∘ρ∘F) ≤ ε`
   Equivalent to `sdist ≤ ε` and `ContextEquiv ε`.

2. **`RHP`** (paper's notion, with simulator):
   `∀A ∃S, RobustCompilation ε (bind π (mapSum pure A)) (bind F (mapSum pure S))`
   Equivalent to `UCEmulates ε`.
   Reference: Patrignani, Wahby et al., "UC is RC", TOPLAS 2024.

3. **`UCEmulates`** (Canetti-style):
   `∀A ∃S, sdist(bind π (mapSum pure A), bind F (mapSum pure S)) ≤ ε`

## Relationship diagram

```
  sdist ≤ ε  ↔  ContextEquiv ε  ↔  RobustCompilation ε  (no simulator)
      ↓ (one direction only: take S = A)
  UCEmulates ε  ↔  RHP ε  (with ∃ simulator)
```

The downward arrow is strict: UC/RHP is strictly weaker than sdist/RC.
Counterexample: `π = pure(.inr true)`, `F = pure(.inr false)`,
`S = fun b => pure (not b)` gives UC with `ε = 0` but `sdist π F > 0`.

## Main definitions

* `compile` — substitute a subroutine implementation into a protocol
* `ContextEquiv` — contextual equivalence (all distinguishers bounded)
* `RobustCompilation` — RC without simulator: all contexts bounded
* `RHP` — RC with simulator: paper's "Robust Hyperproperties Preservation"

## Main results

* `contextEquiv_iff_sdist` — `ContextEquiv ε ↔ sdist ≤ ε`
* `RC_iff_sdist` — `RobustCompilation ε ↔ sdist ≤ ε`
* `UCEmulates_iff_RHP` — `UCEmulates ε ↔ RHP ε` (the paper's main theorem)
* `sdist_implies_UCEmulates` — `sdist ≤ ε → UCEmulates ε` (one direction)
* `RC_implies_UCEmulates` — `RC → UC` (same-interface)
* `sdist_mapSum_le` — coproduct tensor: `max(ε₁, ε₂)` bound

## Sub-SMC structure

Our `RobustCompilation` (equivalently, `sdist`) forms a **wide sub-SMC** of
`Kl(SPComp)` via `sdist_comp_add` (composition) and `sdist_mapSum_le` (tensor).

UC/RHP inherits this structure in the same-interface case (`leak = sim_if`)
via `UCEmulates_trans` (simulator chaining) and `UCEmulates_of_sdist`.
For the general case (different interfaces), the categorical structure is
richer and involves simulator composition — a 2-categorical notion.
-/

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob

open scoped ENNReal

/-! ## Compile -/

/-- Substitute subroutine `impl` into protocol `ρ`:
    `compile ρ impl = (id ⊕ impl) ∘ₖ ρ`. -/
noncomputable def compile {α β γ δ : Type*}
    (ρ : α → SPComp (β ⊕ γ)) (impl : γ → SPComp δ) :
    α → SPComp (β ⊕ δ) :=
  fun a => SPComp.bind (ρ a) (mapSum SPComp.pure impl)

/-! ## Contextual Equivalence -/

/-- Two morphisms are `ε`-contextually equivalent if no closing context
    (distinguisher `D : β → SPComp Bool`) can distinguish them by more than `ε`. -/
def ContextEquiv {α β : Type*} (ε : ℝ≥0∞) (f g : α → SPComp β) : Prop :=
  ∀ (D : β → SPComp Bool),
    sdist (fun a => SPComp.bind (f a) D) (fun a => SPComp.bind (g a) D) ≤ ε

/-- `sdist ≤ ε → ContextEquiv ε` via right PPL. -/
theorem contextEquiv_of_sdist {α β : Type*} {f g : α → SPComp β} {ε : ℝ≥0∞}
    (h : sdist f g ≤ ε) : ContextEquiv ε f g := by
  intro D
  exact le_trans (sdist_comp_right f g D) h

/-- `ContextEquiv ε → sdist ≤ ε`: the identity distinguisher witnesses the bound.

    For any `f g : α → SPComp β`, `sdist f g = sup_D sdist (D ∘ f) (D ∘ g)`.
    When `β = Bool`, `D = pure` gives `sdist (pure ∘ f) (pure ∘ g) = sdist f g`
    (by bind_pure). For general β, the sdist already takes the sup over D. -/
@[grind →] theorem sdist_of_contextEquiv {α β : Type*} {f g : α → SPComp β} {ε : ℝ≥0∞}
    (h : ContextEquiv ε f g) : sdist f g ≤ ε := by
  -- sdist f g = sup_D sup_a sup_h₀ absDiff(prTrue(bind(f a) D, h₀), ...)
  -- For each D, h D gives sdist(bind f D, bind g D) ≤ ε.
  -- Specializing the inner D' to `pure` and using bind_pure recovers the original.
  unfold sdist
  apply iSup_le; intro D
  apply iSup_le; intro a
  apply iSup_le; intro h₀
  -- Goal: absDiff(prTrue(bind(f a) D, h₀), prTrue(bind(g a) D, h₀)) ≤ ε
  -- From h D : sdist(fun x => bind(f x) D, fun x => bind(g x) D) ≤ ε
  -- = sup_{D' a' h₀'} absDiff(prTrue(bind(bind(f a') D) D', h₀'), ...) ≤ ε
  -- Specialize D' = pure, a' = a, h₀' = h₀:
  -- bind(bind(f a) D) pure = bind(f a) D  (by bind_pure)
  have key : absDiff (prTrue (SPComp.bind (f a) D) h₀)
      (prTrue (SPComp.bind (g a) D) h₀) ≤ sdist (fun x => SPComp.bind (f x) D)
        (fun x => SPComp.bind (g x) D) := by
    have : absDiff (prTrue (SPComp.bind (SPComp.bind (f a) D) SPComp.pure) h₀)
        (prTrue (SPComp.bind (SPComp.bind (g a) D) SPComp.pure) h₀)
        ≤ sdist (fun x => SPComp.bind (f x) D) (fun x => SPComp.bind (g x) D) :=
      sdist_le_of_forall le_rfl SPComp.pure a h₀
    simp only [SPComp.bind_pure] at this
    exact this
  exact le_trans key (h D)

/-- Contextual equivalence iff bounded sdist. -/
theorem contextEquiv_iff_sdist {α β : Type*} (f g : α → SPComp β) (ε : ℝ≥0∞) :
    ContextEquiv ε f g ↔ sdist f g ≤ ε :=
  ⟨sdist_of_contextEquiv, contextEquiv_of_sdist⟩

/-! ## Robust Compilation -/

/-- Robust Compilation: replacing subroutine `F` with `π` preserves security
    in ALL contexts `ρ` and for ALL distinguishers. -/
def RobustCompilation {I O : Type} (ε : ℝ≥0∞) (π F : I → SPComp O) : Prop :=
  ∀ (γ : Type) (ρ : γ → SPComp I) (D : O → SPComp Bool),
    sdist (fun c => SPComp.bind (SPComp.bind (ρ c) π) D)
          (fun c => SPComp.bind (SPComp.bind (ρ c) F) D) ≤ ε

/-- `sdist ≤ ε → RC`: both PPLs give the bound. -/
theorem RC_of_sdist {I O : Type} {π F : I → SPComp O} {ε : ℝ≥0∞}
    (h : sdist π F ≤ ε) : RobustCompilation ε π F := by
  intro γ ρ D
  -- bind (ρ c) π is pre-composition, bind D is post-composition
  -- sdist (D ∘ π ∘ ρ) (D ∘ F ∘ ρ)
  --   ≤ sdist (π ∘ ρ) (F ∘ ρ)   -- right PPL (post-comp with D)
  --   ≤ sdist π F               -- left PPL (pre-comp with ρ)
  --   ≤ ε
  calc sdist (fun c => SPComp.bind (SPComp.bind (ρ c) π) D)
             (fun c => SPComp.bind (SPComp.bind (ρ c) F) D)
      ≤ sdist (fun c => SPComp.bind (ρ c) π)
              (fun c => SPComp.bind (ρ c) F) :=
        sdist_comp_right _ _ D
    _ ≤ sdist π F := sdist_comp_left ρ π F
    _ ≤ ε := h

/-- `RC → sdist ≤ ε`: specialize to `ρ = pure` (identity context). -/
@[grind →] theorem sdist_of_RC {I O : Type} {π F : I → SPComp O} {ε : ℝ≥0∞}
    (h : RobustCompilation ε π F) : sdist π F ≤ ε := by
  -- Specialize RC with γ = I, ρ = pure
  -- Then bind (pure c) π = π c, and the RC bound gives sdist bound.
  -- RC says: ∀ γ ρ D, sdist(fun c => bind(bind(ρ c) π) D, ...) ≤ ε
  -- With ρ = pure: sdist(fun c => bind (π c) D, fun c => bind (F c) D) ≤ ε
  -- We need to extract from this the pointwise bound.
  unfold sdist
  apply iSup_le; intro D
  apply iSup_le; intro a
  apply iSup_le; intro h₀
  -- From h I pure D: sdist(fun c => bind (π c) D, fun c => bind (F c) D) ≤ ε
  have hspec := h I SPComp.pure D
  simp only [SPComp.pure_bind] at hspec
  -- hspec : sdist (fun c => bind (π c) D) (fun c => bind (F c) D) ≤ ε
  -- Specialize the inner sdist with D' = pure, a, h₀
  have key : absDiff (prTrue (SPComp.bind (π a) D) h₀)
      (prTrue (SPComp.bind (F a) D) h₀) ≤
      sdist (fun c => SPComp.bind (π c) D) (fun c => SPComp.bind (F c) D) := by
    have := @sdist_le_of_forall _ _ (fun c => SPComp.bind (π c) D)
      (fun c => SPComp.bind (F c) D) _ le_rfl SPComp.pure a h₀
    simp only [SPComp.bind_pure] at this
    exact this
  exact le_trans key hspec

/-- RC ↔ sdist ≤ ε. -/
theorem RC_iff_sdist {I O : Type} (π F : I → SPComp O) (ε : ℝ≥0∞) :
    RobustCompilation ε π F ↔ sdist π F ≤ ε :=
  ⟨sdist_of_RC, RC_of_sdist⟩

/-! ## UC from sdist (Same Interface) -/

/-- sdist → UC (same-interface): the simulator is the adversary.

    When `sdist π F ≤ ε`, UC emulation holds with S = A for any adversary A.
    The reverse implication is FALSE: UC emulation allows the simulator
    to transform F's leak channel, so `∃ S, sdist π (bind F (mapSum pure S)) ≤ ε`
    does not imply `sdist π F ≤ ε`. -/
theorem sdist_implies_UCEmulates {hon out leak view : Type*} (ε : ℝ≥0∞)
    (π F : hon → SPComp (out ⊕ leak))
    (h : sdist π F ≤ ε) :
    UCEmulates ε ⟨hon, out, leak, leak, view⟩ π F :=
  UCEmulates_of_sdist ε π F h

/-- RC → UC (same-interface): since RC ↔ sdist, RC also implies UC. -/
theorem RC_implies_UCEmulates {hon out leak view : Type} (ε : ℝ≥0∞)
    (π F : hon → SPComp (out ⊕ leak))
    (h : RobustCompilation ε π F) :
    UCEmulates ε ⟨hon, out, leak, leak, view⟩ π F :=
  sdist_implies_UCEmulates ε π F (sdist_of_RC h)

/-! ## Robust Hyperproperties Preservation (RHP)

The paper "Universal Composability is Robust Compilation" (Patrignani, Wahby et al., 2024)
defines a different notion of Robust Compilation that includes an existential simulator.
We call this RHP (Robust Hyperproperties Preservation) to distinguish it from our
simulator-free `RobustCompilation`.

The key difference:
- Our `RobustCompilation`: `∀ ρ D, dist(D∘ρ∘π, D∘ρ∘F) ≤ ε` (no simulator)
- Paper's RHP: `∀A ∃S, ∀ ρ D, dist(D∘ρ∘(id⊕A)∘π, D∘ρ∘(id⊕S)∘F) ≤ ε`

Since `RobustCompilation ↔ sdist` (our `RC_iff_sdist`), RHP reduces to:
`∀A ∃S, sdist(bind π (mapSum pure A), bind F (mapSum pure S)) ≤ ε`,
which is exactly `UCEmulates`. Hence UC ↔ RHP at Level 1.

The relationship diagram:
```
  sdist ≤ ε  ↔  ContextEquiv ε  ↔  RobustCompilation ε  (no simulator)
      ↓ (one direction only: take S = A)
  UCEmulates ε  ↔  RHP ε  (with ∃ simulator)
```
-/

/-- Robust Hyperproperties Preservation: the paper's notion of Robust Compilation.

    Unlike our `RobustCompilation` (which has no simulator), RHP includes an
    existential simulator (`∀A ∃S`), matching the quantifier structure of UC.

    RHP says: for all adversaries A, there exists a simulator S such that the
    post-adversary views are robustly equivalent in ALL contexts.

    Reference: Patrignani, Wahby et al., "Universal Composability is Robust
    Compilation", TOPLAS 2024. -/
def RHP (ε : ℝ≥0∞) (hon out leak sim_if view : Type)
    (π : hon → SPComp (out ⊕ leak))
    (F : hon → SPComp (out ⊕ sim_if)) : Prop :=
  ∀ (A : leak → SPComp view),
    ∃ (S : sim_if → SPComp view),
      RobustCompilation ε
        (fun a => SPComp.bind (π a) (mapSum SPComp.pure A))
        (fun a => SPComp.bind (F a) (mapSum SPComp.pure S))

/-- UC → RHP: UC gives `sdist ≤ ε`, then `RC_of_sdist` lifts to all contexts. -/
theorem RHP_of_UCEmulates {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    {π : hon → SPComp (out ⊕ leak)}
    {F : hon → SPComp (out ⊕ sim_if)}
    (h : UCEmulates ε ⟨hon, out, leak, sim_if, view⟩ π F) :
    RHP ε hon out leak sim_if view π F := by
  intro A
  obtain ⟨S, hS⟩ := h A
  exact ⟨S, RC_of_sdist hS⟩

/-- RHP → UC: specializing the RHP contexts recovers `sdist ≤ ε`. -/
theorem UCEmulates_of_RHP {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    {π : hon → SPComp (out ⊕ leak)}
    {F : hon → SPComp (out ⊕ sim_if)}
    (h : RHP ε hon out leak sim_if view π F) :
    UCEmulates ε ⟨hon, out, leak, sim_if, view⟩ π F := by
  intro A
  obtain ⟨S, hS⟩ := h A
  exact ⟨S, sdist_of_RC hS⟩

/-- UC ↔ RHP at Level 1 (information-theoretic).

    This is the main theorem of Patrignani, Wahby et al. (2024):
    "Universal Composability is Robust Compilation".

    At Level 1 (no complexity bounds), the equivalence is immediate because
    `RobustCompilation ↔ sdist` (our `RC_iff_sdist`), so the ∀-context
    quantification in RHP adds no strength beyond sdist.

    At computational levels (Level 2/3), RHP quantifies over poly-time contexts
    while sdist takes a sup over ALL distinguishers. The equivalence then
    requires the dummy adversary theorem and becomes non-trivial. -/
theorem UCEmulates_iff_RHP {hon out leak sim_if view : Type}
    (π : hon → SPComp (out ⊕ leak))
    (F : hon → SPComp (out ⊕ sim_if)) (ε : ℝ≥0∞) :
    UCEmulates ε ⟨hon, out, leak, sim_if, view⟩ π F ↔
    RHP ε hon out leak sim_if view π F :=
  ⟨RHP_of_UCEmulates, UCEmulates_of_RHP⟩

/-! ## Tensor Distance Bounds -/

/-- For coproduct tensor: distance is max, not sum, since only one branch runs. -/
theorem sdist_mapSum_le {α₁ α₂ β₁ β₂ : Type*}
    (f₁ f₂ : α₁ → SPComp α₂) (g₁ g₂ : β₁ → SPComp β₂)
    {ε₁ ε₂ : ℝ≥0∞} (hf : sdist f₁ f₂ ≤ ε₁) (hg : sdist g₁ g₂ ≤ ε₂) :
    sdist (mapSum f₁ g₁) (mapSum f₂ g₂) ≤ ε₁ ⊔ ε₂ := by
  apply iSup_le; intro D
  apply iSup_le; intro x
  apply iSup_le; intro h₀
  rcases x with a | c
  · -- .inl a: only f runs
    simp only [mapSum_inl, SPComp.map]
    -- bind (bind (f₁ a) (pure ∘ inl)) D = bind (f₁ a) (D ∘ inl)
    have eq1 : SPComp.bind (SPComp.bind (f₁ a) fun b => SPComp.pure (Sum.inl b)) D =
      SPComp.bind (f₁ a) (fun b => D (Sum.inl b)) := by
      rw [SPComp.bind_assoc]; congr 1; funext b; simp
    have eq2 : SPComp.bind (SPComp.bind (f₂ a) fun b => SPComp.pure (Sum.inl b)) D =
      SPComp.bind (f₂ a) (fun b => D (Sum.inl b)) := by
      rw [SPComp.bind_assoc]; congr 1; funext b; simp
    rw [eq1, eq2]
    calc absDiff (prTrue (SPComp.bind (f₁ a) fun b => D (Sum.inl b)) h₀)
                 (prTrue (SPComp.bind (f₂ a) fun b => D (Sum.inl b)) h₀)
        ≤ sdist f₁ f₂ := by
          apply sdist_le_of_forall le_rfl
      _ ≤ ε₁ := hf
      _ ≤ ε₁ ⊔ ε₂ := le_max_left _ _
  · -- .inr c: only g runs
    simp only [mapSum_inr, SPComp.map]
    have eq1 : SPComp.bind (SPComp.bind (g₁ c) fun d => SPComp.pure (Sum.inr d)) D =
      SPComp.bind (g₁ c) (fun d => D (Sum.inr d)) := by
      rw [SPComp.bind_assoc]; congr 1; funext d; simp
    have eq2 : SPComp.bind (SPComp.bind (g₂ c) fun d => SPComp.pure (Sum.inr d)) D =
      SPComp.bind (g₂ c) (fun d => D (Sum.inr d)) := by
      rw [SPComp.bind_assoc]; congr 1; funext d; simp
    rw [eq1, eq2]
    calc absDiff (prTrue (SPComp.bind (g₁ c) fun d => D (Sum.inr d)) h₀)
                 (prTrue (SPComp.bind (g₂ c) fun d => D (Sum.inr d)) h₀)
        ≤ sdist g₁ g₂ := by
          apply sdist_le_of_forall le_rfl
      _ ≤ ε₂ := hg
      _ ≤ ε₁ ⊔ ε₂ := le_max_right _ _

/-! ## Sequential and Parallel Composition of RC -/

/-- Sequential composition (transitivity) of robust compilation.

    If `π₁ ≈_{ε₁} π₂` and `π₂ ≈_{ε₂} π₃`, then `π₁ ≈_{ε₁+ε₂} π₃`.
    Proof: `RC ↔ sdist` + triangle inequality. -/
theorem RobustCompilation_trans {I O : Type} {π₁ π₂ π₃ : I → SPComp O}
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : RobustCompilation ε₁ π₁ π₂) (h₂ : RobustCompilation ε₂ π₂ π₃) :
    RobustCompilation (ε₁ + ε₂) π₁ π₃ :=
  RC_of_sdist (le_trans (sdist_triangle π₁ π₂ π₃)
    (add_le_add (sdist_of_RC h₁) (sdist_of_RC h₂)))

/-- Parallel composition of robust compilation via coproduct tensor.

    The max bound (not sum!) reflects the coproduct structure: each input
    activates exactly one sub-protocol, so the distances don't accumulate. -/
theorem RobustCompilation_mapSum {α₁ β₁ α₂ β₂ : Type}
    {ε₁ ε₂ : ℝ≥0∞}
    {π₁ F₁ : α₁ → SPComp β₁} {π₂ F₂ : α₂ → SPComp β₂}
    (h₁ : RobustCompilation ε₁ π₁ F₁) (h₂ : RobustCompilation ε₂ π₂ F₂) :
    RobustCompilation (ε₁ ⊔ ε₂) (mapSum π₁ π₂) (mapSum F₁ F₂) :=
  RC_of_sdist (sdist_mapSum_le π₁ F₁ π₂ F₂ (sdist_of_RC h₁) (sdist_of_RC h₂))

/-! ## Parallel UC Composition -/

/-- Parallel composition of UC-secure protocols (same-interface case).

    Given sdist bounds for two protocols, the parallel composition `mapSum π₁ π₂`
    UC-emulates `mapSum F₁ F₂` with error `max(ε₁, ε₂)`.

    The max bound (not sum!) reflects the coproduct structure: each input
    activates exactly one sub-protocol, so the distances don't accumulate.

    The UC spec treats the combined output `β₁ ⊕ β₂` as the leak interface
    (same-interface: `leak = sim_if`), with `Unit` as the honest output.

    **Practical use**: Multi-instance security (n copies of a protocol),
    or independent sub-protocols running on disjoint message types. -/
theorem UCEmulates_mapSum_of_sdist {α₁ β₁ α₂ β₂ : Type*} {V : Type*}
    {ε₁ ε₂ : ℝ≥0∞}
    (π₁ F₁ : α₁ → SPComp β₁) (π₂ F₂ : α₂ → SPComp β₂)
    (h₁ : sdist π₁ F₁ ≤ ε₁) (h₂ : sdist π₂ F₂ ≤ ε₂) :
    UCEmulates (ε₁ ⊔ ε₂)
      ⟨α₁ ⊕ α₂, Unit, β₁ ⊕ β₂, β₁ ⊕ β₂, V⟩
      (fun x => SPComp.bind (mapSum π₁ π₂ x) (fun o => SPComp.pure (.inr o)))
      (fun x => SPComp.bind (mapSum F₁ F₂ x) (fun o => SPComp.pure (.inr o))) := by
  apply UCEmulates_of_sdist
  exact le_trans (sdist_comp_right _ _ _) (sdist_mapSum_le π₁ F₁ π₂ F₂ h₁ h₂)

end CatCrypt.Crypto
