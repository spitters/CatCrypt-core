/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCAdmClass

/-!
# Patrignani Security Levels 2 and 3

This file defines UC emulation at **Level 2** (computational distinguishers) and
**Level 3** (fully computational: computational distinguishers + poly-time simulators),
following Patrignani et al. ("UC is RC", TOPLAS 2024).

## The Three Levels

| Level | Metric | Adversary | Simulator |
|-------|--------|-----------|-----------|
| **1** (info-theoretic) | `ucSdist` (all D) | ∀ A | ∃ S |
| **2** (comp. distinguishers) | `ucCdist` (adm D only) | ∀ A | ∃ S |
| **3** (fully computational) | `ucCdist` (adm D only) | ∀ A | ∃ S, adm S |

## Hierarchy

```
L1 → L2 (via ucCdist ≤ ucSdist)
L3 → L2 (forget adm S)
L2 ⊬ L3 (S = A may not be admissible)
```

## Main definitions

* `UCEmulatesL2` — Level 2 UC emulation (computational distinguishers)
* `UCEmulatesL3` — Level 3 UC emulation (fully computational)
* `SimConstruction.admPreserving` — simulator preserves admissibility
* `UCEmulatesAlgL3` — algebraic Level 3 with explicit simulator construction

## Main results

* `UCEmulatesL2_of_L1` — Level 1 implies Level 2
* `UCEmulatesL3_implies_L2` — Level 3 implies Level 2
* `UCEmulatesL2_of_sdist` — same-interface from sdist bound
* `UCEmulatesL2_refl`, `_trans`, `_mono` — structural properties
* `UCEmulatesL3_refl_adm`, `_trans`, `_mono` — structural properties
-/

@[expose] public section

open scoped ENNReal

namespace UCMonad

variable {T : Type → Type}

/-! ## Section 1: Level 2 — Computational Distinguishers -/

/-- Level 2 UC emulation: for ALL adversaries A, there EXISTS a simulator S
    such that the **computational** distance between the views is ≤ ε.

    The metric is `ucCdist` (supremum over admissible distinguishers only),
    but there is NO restriction on A or S. -/
def UCEmulatesL2 [UCMonadCompDist T] (ε : ℝ≥0∞)
    {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak))
    (F : hon → T (out ⊕ sim_if)) : Prop :=
  ∀ (A : leak → T view), ∃ (S : sim_if → T view),
    ucCdist (fun a => π a >>= UCMonadBase.ucMapSum pure A)
            (fun a => F a >>= UCMonadBase.ucMapSum pure S) ≤ ε

/-! ### Level 2: Hierarchy -/

/-- Level 1 implies Level 2: `ucCdist ≤ ucSdist` gives the implication.

    This is the fundamental hierarchy theorem: info-theoretic security
    implies computational security. -/
theorem UCEmulatesL2_of_L1 [UCMonadCompDist T]
    {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    {π : hon → T (out ⊕ leak)} {F : hon → T (out ⊕ sim_if)}
    (h : UCEmulates (T := T) (view := view) ε π F) :
    UCEmulatesL2 (T := T) (view := view) ε π F := by
  intro A
  obtain ⟨S, hS⟩ := h A
  exact ⟨S, le_trans (ucCdist_le_ucSdist _ _) hS⟩

/-- Same-interface Level 2 from sdist bound (unconditional).

    The simulator is `S = A` (dummy adversary). The bound follows from
    `ucCdist ≤ ucSdist` and right PPL for `ucSdist`. -/
theorem UCEmulatesL2_of_sdist [UCMonadCompDist T]
    {hon out leak view : Type} (ε : ℝ≥0∞)
    (π F : hon → T (out ⊕ leak))
    (h : UCMonadMetric.ucSdist π F ≤ ε) :
    UCEmulatesL2 (T := T) (view := view) ε π F :=
  UCEmulatesL2_of_L1 (UCEmulates_of_sdist ε π F h)

/-! ### Level 2: Structural Properties -/

/-- Monotonicity for Level 2. -/
theorem UCEmulatesL2_mono [UCMonadCompDist T]
    {hon out leak sim_if view : Type}
    {π : hon → T (out ⊕ leak)} {F : hon → T (out ⊕ sim_if)}
    {ε₁ ε₂ : ℝ≥0∞}
    (h : UCEmulatesL2 (T := T) (view := view) ε₁ π F) (hle : ε₁ ≤ ε₂) :
    UCEmulatesL2 (T := T) (view := view) ε₂ π F := by
  intro A
  obtain ⟨S, hS⟩ := h A
  exact ⟨S, le_trans hS hle⟩

/-- Reflexivity for Level 2. -/
theorem UCEmulatesL2_refl [UCMonadCompDist T]
    {hon out leak view : Type}
    (π : hon → T (out ⊕ leak)) :
    UCEmulatesL2 (T := T) (view := view) 0 π π := by
  intro A
  exact ⟨A, by simp [ucCdist_self]⟩

/-- Transitivity for Level 2 (same-interface). -/
theorem UCEmulatesL2_trans [UCMonadCompDist T]
    {hon out leak view : Type} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ π₂ π₃ : hon → T (out ⊕ leak)}
    (h₁ : UCEmulatesL2 (T := T) (view := view) ε₁ π₁ π₂)
    (h₂ : UCEmulatesL2 (T := T) (view := view) ε₂ π₂ π₃) :
    UCEmulatesL2 (T := T) (view := view) (ε₁ + ε₂) π₁ π₃ := by
  intro A
  obtain ⟨S₁, hS₁⟩ := h₁ A
  obtain ⟨S₂, hS₂⟩ := h₂ S₁
  exact ⟨S₂, le_trans (ucCdist_triangle _ _ _) (add_le_add hS₁ hS₂)⟩

/-! ## Section 2: Level 3 — Fully Computational -/

/-- Level 3 UC emulation: for ALL adversaries A, there EXISTS an **admissible**
    simulator S such that the computational distance is ≤ ε.

    This is the strongest computational level: both the metric and the simulator
    are restricted to admissible (e.g., poly-time) computations. -/
def UCEmulatesL3 [UCMonadCompDist T] (ε : ℝ≥0∞)
    {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak))
    (F : hon → T (out ⊕ sim_if)) : Prop :=
  ∀ (A : leak → T view), ∃ (S : sim_if → T view),
    adm S ∧
    ucCdist (fun a => π a >>= UCMonadBase.ucMapSum pure A)
            (fun a => F a >>= UCMonadBase.ucMapSum pure S) ≤ ε

/-! ### Level 3 → Level 2 -/

/-- Level 3 implies Level 2: forget the admissibility constraint on S. -/
theorem UCEmulatesL3_implies_L2 [UCMonadCompDist T]
    {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    {π : hon → T (out ⊕ leak)} {F : hon → T (out ⊕ sim_if)}
    (h : UCEmulatesL3 (T := T) (view := view) ε π F) :
    UCEmulatesL2 (T := T) (view := view) ε π F := by
  intro A
  obtain ⟨S, _, hS⟩ := h A
  exact ⟨S, hS⟩

/-! ### Level 3: Structural Properties -/

/-- Monotonicity for Level 3. -/
theorem UCEmulatesL3_mono [UCMonadCompDist T]
    {hon out leak sim_if view : Type}
    {π : hon → T (out ⊕ leak)} {F : hon → T (out ⊕ sim_if)}
    {ε₁ ε₂ : ℝ≥0∞}
    (h : UCEmulatesL3 (T := T) (view := view) ε₁ π F) (hle : ε₁ ≤ ε₂) :
    UCEmulatesL3 (T := T) (view := view) ε₂ π F := by
  intro A
  obtain ⟨S, hS_adm, hS⟩ := h A
  exact ⟨S, hS_adm, le_trans hS hle⟩

/-- Reflexivity for Level 3 with admissible adversaries.

    Level 3 reflexivity uses `S = A`, which requires `adm A`.
    This is the fundamental Level 2 vs Level 3 gap:
    Level 2 reflexivity is unconditional, Level 3 is conditional. -/
theorem UCEmulatesL3_refl_adm [UCMonadCompDist T]
    {hon out leak view : Type}
    (π : hon → T (out ⊕ leak))
    (hA : ∀ (A : leak → T view), adm A) :
    UCEmulatesL3 (T := T) (view := view) 0 π π := by
  intro A
  exact ⟨A, hA A, by simp [ucCdist_self]⟩

/-- Transitivity for Level 3 (same-interface). -/
theorem UCEmulatesL3_trans [UCMonadCompDist T]
    {hon out leak view : Type} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ π₂ π₃ : hon → T (out ⊕ leak)}
    (h₁ : UCEmulatesL3 (T := T) (view := view) ε₁ π₁ π₂)
    (h₂ : UCEmulatesL3 (T := T) (view := view) ε₂ π₂ π₃) :
    UCEmulatesL3 (T := T) (view := view) (ε₁ + ε₂) π₁ π₃ := by
  intro A
  obtain ⟨S₁, hS₁_adm, hS₁⟩ := h₁ A
  obtain ⟨S₂, hS₂_adm, hS₂⟩ := h₂ S₁
  exact ⟨S₂, hS₂_adm, le_trans (ucCdist_triangle _ _ _) (add_le_add hS₁ hS₂)⟩

/-! ## Section 3: Algebraic Level 3 -/

/-- A simulator construction preserves admissibility:
    if A is admissible, then Sim(A) is admissible.

    This is the key property needed for Level 3 algebraic UC emulation. -/
def SimConstruction.admPreserving [Monad T] [UCMonadBase T] [UCAdmClass T]
    {leak sim_if view : Type}
    (Sim : SimConstruction T leak sim_if view) : Prop :=
  ∀ (A : leak → T view), adm A → adm (Sim A)

/-- The identity simulator construction preserves admissibility. -/
theorem SimConstruction.id_admPreserving [Monad T] [UCMonadBase T] [UCAdmClass T]
    {leak view : Type} :
    (SimConstruction.id (T := T) (leak := leak) (view := view)).admPreserving :=
  fun _ hA => hA

/-- Composition of admissibility-preserving simulators preserves admissibility. -/
theorem SimConstruction.comp_admPreserving [Monad T] [UCMonadBase T] [UCAdmClass T]
    {leak₁ leak₂ leak₃ view : Type}
    {Sim₁ : SimConstruction T leak₁ leak₂ view}
    {Sim₂ : SimConstruction T leak₂ leak₃ view}
    (h₁ : Sim₁.admPreserving) (h₂ : Sim₂.admPreserving) :
    (SimConstruction.comp Sim₁ Sim₂).admPreserving :=
  fun A hA => h₂ (Sim₁ A) (h₁ A hA)

/-- Algebraic Level 3 UC emulation: explicit simulator construction that
    preserves admissibility and achieves the computational distance bound. -/
def UCEmulatesAlgL3 [UCMonadCompDist T] (ε : ℝ≥0∞)
    {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak))
    (F : hon → T (out ⊕ sim_if))
    (Sim : SimConstruction T leak sim_if view) : Prop :=
  Sim.admPreserving ∧
  ∀ (A : leak → T view),
    ucCdist (fun a => π a >>= UCMonadBase.ucMapSum pure A)
            (fun a => F a >>= UCMonadBase.ucMapSum pure (Sim A)) ≤ ε

/-- Algebraic Level 3 forgets to Level 3 (for admissible adversaries). -/
theorem UCEmulatesAlgL3_forget_L3 [UCMonadCompDist T]
    {ε : ℝ≥0∞} {hon out leak sim_if view : Type}
    {π : hon → T (out ⊕ leak)}
    {F : hon → T (out ⊕ sim_if)}
    {Sim : SimConstruction T leak sim_if view}
    (h : UCEmulatesAlgL3 (T := T) ε π F Sim) :
    ∀ (A : leak → T view), adm A →
      ∃ (S : sim_if → T view), adm S ∧
        ucCdist (fun a => π a >>= UCMonadBase.ucMapSum pure A)
                (fun a => F a >>= UCMonadBase.ucMapSum pure S) ≤ ε :=
  fun A hA => ⟨Sim A, h.1 A hA, h.2 A⟩

/-- Algebraic Level 3 forgets to Level 2 (unconditionally). -/
theorem UCEmulatesAlgL3_to_L2 [UCMonadCompDist T]
    {ε : ℝ≥0∞} {hon out leak sim_if view : Type}
    {π : hon → T (out ⊕ leak)}
    {F : hon → T (out ⊕ sim_if)}
    {Sim : SimConstruction T leak sim_if view}
    (h : UCEmulatesAlgL3 (T := T) ε π F Sim) :
    UCEmulatesL2 (T := T) (view := view) ε π F :=
  fun A => ⟨Sim A, h.2 A⟩

/-- Reflexivity for algebraic Level 3 with identity simulator. -/
theorem UCEmulatesAlgL3_refl [UCMonadCompDist T]
    {hon out leak view : Type}
    (π : hon → T (out ⊕ leak)) :
    UCEmulatesAlgL3 (T := T) (view := view) 0 π π
      (SimConstruction.id (T := T) (leak := leak) (view := view)) :=
  ⟨SimConstruction.id_admPreserving, fun _ => le_of_eq (ucCdist_self _)⟩

/-- Monotonicity for algebraic Level 3. -/
theorem UCEmulatesAlgL3_mono [UCMonadCompDist T]
    {ε₁ ε₂ : ℝ≥0∞} {hon out leak sim_if view : Type}
    {π : hon → T (out ⊕ leak)}
    {F : hon → T (out ⊕ sim_if)}
    {Sim : SimConstruction T leak sim_if view}
    (h : UCEmulatesAlgL3 (T := T) ε₁ π F Sim) (hle : ε₁ ≤ ε₂) :
    UCEmulatesAlgL3 (T := T) ε₂ π F Sim :=
  ⟨h.1, fun A => le_trans (h.2 A) hle⟩

/-- Transitivity for algebraic Level 3 via simulator composition. -/
theorem UCEmulatesAlgL3_trans [UCMonadCompDist T]
    {hon out leak view : Type} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ π₂ π₃ : hon → T (out ⊕ leak)}
    {Sim₁ Sim₂ : SimConstruction T leak leak view}
    (h₁ : UCEmulatesAlgL3 (T := T) ε₁ π₁ π₂ Sim₁)
    (h₂ : UCEmulatesAlgL3 (T := T) ε₂ π₂ π₃ Sim₂) :
    UCEmulatesAlgL3 (T := T) (ε₁ + ε₂) π₁ π₃ (Sim₂ ∘ Sim₁) :=
  ⟨SimConstruction.comp_admPreserving h₁.1 h₂.1,
   fun A => le_trans (ucCdist_triangle _ _ _) (add_le_add (h₁.2 A) (h₂.2 (Sim₁ A)))⟩

/-! ## Section 3b: Lifting ucSdist to Algebraic Level 3 -/

/-- Lift a same-interface `ucSdist` bound to `UCEmulatesAlgL3` with `SimConstruction.id`.

    Since `SimConstruction.id` preserves admissibility for ANY `UCAdmClass`
    (not just trivial), this works for genuine computational admissibility.
    The bound follows from `ucCdist ≤ ucSdist` and right PPL for `ucSdist`. -/
theorem UCEmulatesAlgL3_of_ucSdist [UCMonadCompDist T]
    {ε : ℝ≥0∞} {hon out leak view : Type}
    (π F : hon → T (out ⊕ leak))
    (h : UCMonadMetric.ucSdist π F ≤ ε) :
    UCEmulatesAlgL3 (T := T) (view := view) ε π F SimConstruction.id :=
  ⟨SimConstruction.id_admPreserving, fun A =>
    le_trans (ucCdist_le_ucSdist _ _)
      (le_trans (UCMonadMetric.ucSdist_comp_right π F
        (UCMonadBase.ucMapSum pure A)) h)⟩

/-! ## Section 4: Dummy Adversary Analysis -/

/-- The dummy adversary theorem for Level 2 (via sdist).

    For same-interface protocols, if `ucSdist π F ≤ ε`, then `UCEmulatesL2 ε π F`
    with `S = A` for all adversaries. -/
theorem dummy_adversary_L2 [UCMonadCompDist T]
    {hon out leak view : Type} (ε : ℝ≥0∞)
    (π F : hon → T (out ⊕ leak))
    (h : UCMonadMetric.ucSdist π F ≤ ε) :
    UCEmulatesL2 (T := T) (view := view) ε π F :=
  UCEmulatesL2_of_sdist ε π F h

/-- The dummy adversary for Level 3 requires admissible adversaries.

    Unlike Level 2, we cannot use S = A unconditionally because S must be admissible.
    This theorem provides the Level 3 bound when A is known to be admissible. -/
theorem dummy_adversary_L3_restricted [UCMonadCompDist T]
    {hon out leak view : Type} (ε : ℝ≥0∞)
    (π F : hon → T (out ⊕ leak))
    (h : UCMonadMetric.ucSdist π F ≤ ε) :
    ∀ (A : leak → T view), adm A →
      ∃ (S : leak → T view), adm S ∧
        ucCdist (fun a => π a >>= UCMonadBase.ucMapSum pure A)
                (fun a => F a >>= UCMonadBase.ucMapSum pure S) ≤ ε := by
  intro A hA
  refine ⟨A, hA, ?_⟩
  calc ucCdist (fun a => π a >>= UCMonadBase.ucMapSum pure A)
               (fun a => F a >>= UCMonadBase.ucMapSum pure A)
      ≤ UCMonadMetric.ucSdist π F :=
        le_trans (ucCdist_le_ucSdist _ _)
          (UCMonadMetric.ucSdist_comp_right π F (UCMonadBase.ucMapSum pure A))
    _ ≤ ε := h

/-! ## Section 5: Level Summary -/

/-- The complete implication chain:
    L1(ε) → L2(ε) [via ucCdist ≤ ucSdist]
    L3(ε) → L2(ε) [forget adm S]
    L2(ε) does NOT imply L3(ε) in general [S = A may not be admissible] -/
theorem levels_hierarchy [UCMonadCompDist T]
    {hon out leak view : Type} {ε : ℝ≥0∞}
    {π₁ π₂ : hon → T (out ⊕ leak)} :
    (UCEmulates (T := T) (view := view) ε π₁ π₂ →
      UCEmulatesL2 (T := T) (view := view) ε π₁ π₂) ∧
    (UCEmulatesL3 (T := T) (view := view) ε π₁ π₂ →
      UCEmulatesL2 (T := T) (view := view) ε π₁ π₂) :=
  ⟨UCEmulatesL2_of_L1, UCEmulatesL3_implies_L2⟩

end UCMonad
