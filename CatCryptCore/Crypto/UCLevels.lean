/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCAdmClass

/-!
# Security levels 2 and 3

This file defines UC emulation at level 2, over the computational distance `ucCdist`
(admissible distinguishers), and at level 3, which in addition requires an admissible
simulator. Level 1 is the statistical emulation `UCEmulates` over `ucSdist`. The file proves
that level 1 and level 3 each imply level 2, and reflexivity, transitivity and monotonicity
for levels 2 and 3 and for the algebraic level 3 with an explicit simulator construction.

| Level | Metric | Adversary | Simulator |
|-------|--------|-----------|-----------|
| 1 | `ucSdist` (all D) | ∀ A | ∃ S |
| 2 | `ucCdist` (admissible D) | ∀ A | ∃ S |
| 3 | `ucCdist` (admissible D) | ∀ A | ∃ S, adm S |

## Main definitions

* `UCEmulatesL2` — level 2 UC emulation
* `UCEmulatesL3` — level 3 UC emulation
* `SimConstruction.admPreserving` — a simulator construction preserves admissibility
* `UCEmulatesAlgL3` — level 3 with an explicit simulator construction

## Main results

* `UCEmulatesL2_of_L1` — level 1 implies level 2
* `UCEmulatesL3_implies_L2` — level 3 implies level 2
* `levels_hierarchy` — both implications together
* `UCEmulatesL2_of_sdist` — level 2 from an `sdist` bound on same-interface systems
* `UCEmulatesL2_refl`, `UCEmulatesL2_trans`, `UCEmulatesL2_mono`
* `UCEmulatesL3_refl_adm`, `UCEmulatesL3_trans`, `UCEmulatesL3_mono`
* `UCEmulatesAlgL3_refl`, `UCEmulatesAlgL3_trans`, `UCEmulatesAlgL3_mono`

Relation to the literature: `CatCryptCore/Crypto/Complexity.md`.

## References

* Patrignani, Künnemann, Wahby, Cecchetti, "Universal Composability Is Robust
  Compilation", TOPLAS 46(4), 2024 — perfect UC (Def. 2), level 1 at `ε = 0`
* Künnemann, Patrignani, Cecchetti, "Computationally Bounded Robust Compilation and
  Universally Composable Security", CSF 2024 — statistical UC (§IV-A), level 1 at `ε > 0`;
  computational UC (Def. 3); predicate-parametrised robust compilation (Def. 7)
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
  exact fun A => (h A).imp fun _ hS => le_trans (ucCdist_le_ucSdist _ _) hS

/-- Same-interface Level 2 from sdist bound (unconditional).

    The simulator is the identity simulator `S = A`. The bound follows from
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
  exact fun A => (h A).imp fun _ hS => le_trans hS hle

/-- Reflexivity for Level 2. -/
theorem UCEmulatesL2_refl [UCMonadCompDist T]
    {hon out leak view : Type}
    (π : hon → T (out ⊕ leak)) :
    UCEmulatesL2 (T := T) (view := view) 0 π π := by
  exact fun A => ⟨A, by simp [ucCdist_self]⟩

/-- Transitivity for Level 2 (same-interface). -/
theorem UCEmulatesL2_trans [UCMonadCompDist T]
    {hon out leak view : Type} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ π₂ π₃ : hon → T (out ⊕ leak)}
    (h₁ : UCEmulatesL2 (T := T) (view := view) ε₁ π₁ π₂)
    (h₂ : UCEmulatesL2 (T := T) (view := view) ε₂ π₂ π₃) :
    UCEmulatesL2 (T := T) (view := view) (ε₁ + ε₂) π₁ π₃ := by
  exact fun A => (h₁ A).elim fun S₁ hS₁ => (h₂ S₁).imp fun _ hS₂ =>
    le_trans (ucCdist_triangle _ _ _) (add_le_add hS₁ hS₂)

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
  exact fun A => (h A).imp fun _ hS => hS.2

/-! ### Level 3: Structural Properties -/

/-- Monotonicity for Level 3. -/
theorem UCEmulatesL3_mono [UCMonadCompDist T]
    {hon out leak sim_if view : Type}
    {π : hon → T (out ⊕ leak)} {F : hon → T (out ⊕ sim_if)}
    {ε₁ ε₂ : ℝ≥0∞}
    (h : UCEmulatesL3 (T := T) (view := view) ε₁ π F) (hle : ε₁ ≤ ε₂) :
    UCEmulatesL3 (T := T) (view := view) ε₂ π F := by
  exact fun A => (h A).imp fun _ hS => ⟨hS.1, le_trans hS.2 hle⟩

/-- Reflexivity for Level 3 with admissible adversaries.

    Level 3 reflexivity uses `S = A`, which requires `adm A`.
    This is the fundamental Level 2 vs Level 3 gap:
    Level 2 reflexivity is unconditional, Level 3 is conditional. -/
theorem UCEmulatesL3_refl_adm [UCMonadCompDist T]
    {hon out leak view : Type}
    (π : hon → T (out ⊕ leak))
    (hA : ∀ (A : leak → T view), adm A) :
    UCEmulatesL3 (T := T) (view := view) 0 π π := by
  exact fun A => ⟨A, hA A, by simp [ucCdist_self]⟩

/-- Transitivity for Level 3 (same-interface). -/
theorem UCEmulatesL3_trans [UCMonadCompDist T]
    {hon out leak view : Type} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ π₂ π₃ : hon → T (out ⊕ leak)}
    (h₁ : UCEmulatesL3 (T := T) (view := view) ε₁ π₁ π₂)
    (h₂ : UCEmulatesL3 (T := T) (view := view) ε₂ π₂ π₃) :
    UCEmulatesL3 (T := T) (view := view) (ε₁ + ε₂) π₁ π₃ := by
  exact fun A => (h₁ A).elim fun S₁ hS₁ => (h₂ S₁).imp fun _ hS₂ =>
    ⟨hS₂.1, le_trans (ucCdist_triangle _ _ _) (add_le_add hS₁.2 hS₂.2)⟩

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

    `SimConstruction.id` preserves admissibility for every `UCAdmClass`. The bound follows from `ucCdist ≤ ucSdist` and right PPL for `ucSdist`. -/
theorem UCEmulatesAlgL3_of_ucSdist [UCMonadCompDist T]
    {ε : ℝ≥0∞} {hon out leak view : Type}
    (π F : hon → T (out ⊕ leak))
    (h : UCMonadMetric.ucSdist π F ≤ ε) :
    UCEmulatesAlgL3 (T := T) (view := view) ε π F SimConstruction.id :=
  ⟨SimConstruction.id_admPreserving, fun A =>
    le_trans (ucCdist_le_ucSdist _ _)
      (le_trans (UCMonadMetric.ucSdist_comp_right π F
        (UCMonadBase.ucMapSum pure A)) h)⟩

/-! ## Section 4: The identity simulator -/

/-- Level 2 with the identity simulator (via sdist).

    For same-interface protocols, if `ucSdist π F ≤ ε`, then `UCEmulatesL2 ε π F`
    with `S = A` for all adversaries. -/
theorem dummy_adversary_L2 [UCMonadCompDist T]
    {hon out leak view : Type} (ε : ℝ≥0∞)
    (π F : hon → T (out ⊕ leak))
    (h : UCMonadMetric.ucSdist π F ≤ ε) :
    UCEmulatesL2 (T := T) (view := view) ε π F :=
  UCEmulatesL2_of_sdist ε π F h

/-- The identity simulator at Level 3 requires admissible adversaries.

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
  exact fun A hA => ⟨A, hA, le_trans (ucCdist_le_ucSdist _ _)
    (le_trans (UCMonadMetric.ucSdist_comp_right π F (UCMonadBase.ucMapSum pure A)) h)⟩

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
