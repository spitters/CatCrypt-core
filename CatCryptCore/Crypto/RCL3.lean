/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.RC
public import CatCryptCore.Crypto.UCLevels

/-!
# Robust compilation at levels 2 and 3

This file defines robust compilation over the computational distance
(`RobustCompilationL3`: closure under contexts and admissible distinguishers) and the
robust-preservation predicates `RHPL3` and `RHPL2` for a fixed simulator construction. It
proves `RobustCompilationL3 ε` equivalent to `ucCdist ≤ ε`, the algebraic level 3 emulation
`UCEmulatesAlgL3` equivalent to `RHPL3`, level 2 emulation equivalent to `RHPL2`, and
transitivity and parallel composition of `RobustCompilationL3`. These lift the level 1
equivalence `UCEmulates_iff_RHP` of `RC.lean` to the levels of `UCLevels.lean`.

## Main definitions

* `RobustCompilationL3` — robust compilation over `ucCdist`
* `ContextEquivL3` — context equivalence over admissible distinguishers
* `RHPL3`, `RHPL2` — robust preservation for a fixed simulator construction

## Main results

* `RC_L3_iff_ucCdist` — `RobustCompilationL3 ε ↔ ucCdist ≤ ε`
* `UCEmulatesAlgL3_iff_RHPL3` — `UCEmulatesAlgL3 ε ↔ RHPL3 ε`
* `UCEmulatesL2_iff_RHPL2` — `UCEmulatesL2 ε ↔ RHPL2 ε`
* `RHPL2_of_RHPL3` — level 3 preservation implies level 2 preservation
* `RobustCompilationL3_trans`, `RobustCompilationL3_mapSum` — transitivity and parallel
  composition

Relation to the literature: `CatCryptCore/Crypto/Complexity.md`.

## References

* Patrignani, Künnemann, Wahby, Cecchetti, "Universal Composability Is Robust
  Compilation", TOPLAS 46(4), 2024 — perfect UC (Def. 2), robust hyperproperty preservation
  (Def. 4), its equivalence with UC (Thm. 4)
* Künnemann, Patrignani, Cecchetti, "Computationally Bounded Robust Compilation and
  Universally Composable Security", CSF 2024 — statistical UC (§IV-A), computational UC
  (Def. 3), predicate-parametrised robust compilation (Def. 7), Thms. 2 and 3
-/

@[expose] public section

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob UCMonad

open scoped ENNReal

variable {T : Type → Type} [UCMonadCompDist T]

/-! ## Robust Compilation at Level 3 -/

/-- Robust Compilation at Level 3: replacing `F` with `π` preserves security
    in all contexts, where the distinguisher is restricted to admissible arrows. -/
def RobustCompilationL3 {α β : Type} (ε : ℝ≥0∞)
    (π F : α → T β) : Prop :=
  ∀ (γ : Type) (ρ : γ → T α) (D : β → T Bool),
    adm D →
    ucCdist (fun c => ρ c >>= π >>= D)
            (fun c => ρ c >>= F >>= D) ≤ ε

/-- Contextual equivalence at Level 3: all admissible distinguishers bounded. -/
def ContextEquivL3 {α β : Type} (ε : ℝ≥0∞) (f g : α → T β) : Prop :=
  ∀ (D : β → T Bool), adm D →
    ucCdist (fun a => f a >>= D) (fun a => g a >>= D) ≤ ε

/-! ## RC_L3 ↔ ucCdist -/

/-- `ucCdist ≤ ε → ContextEquivL3 ε`: right PPL for admissible D. -/
theorem contextEquivL3_of_ucCdist {α β : Type} {f g : α → T β} {ε : ℝ≥0∞}
    (h : ucCdist f g ≤ ε) : ContextEquivL3 ε f g :=
  fun D hD => le_trans (ucCdist_comp_right f g D hD) h

/-- `ContextEquivL3 ε → ucCdist ≤ ε`: recover via per-distinguisher decomposition.

    For each admissible D, `h D hD` bounds `ucCdist (f >>= D) (g >>= D) ≤ ε`.
    We extract `ucDistComp f g D` using `ucDistComp_bind_right` with inner D' = pure:
    ```
    ucDistComp f g D
      = ucDistComp (f >>= D) (g >>= D) pure   -- bind_right with k=D, D'=pure
      ≤ ucCdist (f >>= D) (g >>= D)           -- le_iSup₂ with adm_pure
      ≤ ε                                      -- h D hD
    ``` -/
theorem ucCdist_of_contextEquivL3 {α β : Type} {f g : α → T β} {ε : ℝ≥0∞}
    (h : ContextEquivL3 ε f g) : ucCdist f g ≤ ε := by
  apply iSup₂_le
  intro D hD
  -- ucDistComp f g D = ucDistComp (f >>= D) (g >>= D) pure
  -- via ucDistComp_bind_right with k=D, D'=pure
  have bind_right := UCMonadCompDist.ucDistComp_bind_right f g D pure
  -- bind_right : ucDistComp (f >>= D) (g >>= D) pure = ucDistComp f g (fun b => D b >>= pure)
  -- D b >>= pure = D b by LawfulMonad
  have eq_D : (fun b => D b >>= pure) = D := by funext b; simp [bind_pure]
  calc UCMonadCompDist.ucDistComp f g D
      = UCMonadCompDist.ucDistComp f g (fun b => D b >>= pure) := by rw [eq_D]
    _ = UCMonadCompDist.ucDistComp (fun a => f a >>= D) (fun a => g a >>= D) pure :=
        bind_right.symm
    _ ≤ ucCdist (fun a => f a >>= D) (fun a => g a >>= D) :=
        le_iSup₂ (f := fun D' _ =>
          UCMonadCompDist.ucDistComp (fun a => f a >>= D) (fun a => g a >>= D) D')
          pure adm_pure
    _ ≤ ε := h D hD

/-- `ucCdist ≤ ε → RC_L3 ε`: both PPLs give the bound. -/
theorem RC_L3_of_ucCdist {α β : Type} {π F : α → T β} {ε : ℝ≥0∞}
    (h : ucCdist π F ≤ ε) : RobustCompilationL3 ε π F := by
  intro γ ρ D hD
  calc ucCdist (fun c => ρ c >>= π >>= D) (fun c => ρ c >>= F >>= D)
      ≤ ucCdist (fun c => ρ c >>= π) (fun c => ρ c >>= F) :=
        ucCdist_comp_right _ _ D hD
    _ ≤ ucCdist π F := ucCdist_comp_left ρ π F
    _ ≤ ε := h

/-- `RC_L3 → ucCdist ≤ ε`: specialize ρ = pure, then use ContextEquivL3. -/
theorem ucCdist_of_RC_L3 {α β : Type} {π F : α → T β} {ε : ℝ≥0∞}
    (h : RobustCompilationL3 ε π F) : ucCdist π F ≤ ε := by
  apply ucCdist_of_contextEquivL3
  intro D hD
  have hspec := h α pure D hD
  -- hspec : ucCdist (fun c => pure c >>= π >>= D) (fun c => pure c >>= F >>= D) ≤ ε
  -- pure c >>= π = π c (monad law), so this is ucCdist (fun c => π c >>= D) (fun c => F c >>= D)
  convert hspec using 2 <;> funext c <;> simp [pure_bind]

/-- RC_L3 ↔ ucCdist ≤ ε. -/
theorem RC_L3_iff_ucCdist {α β : Type} (π F : α → T β) (ε : ℝ≥0∞) :
    RobustCompilationL3 ε π F ↔ ucCdist π F ≤ ε :=
  ⟨ucCdist_of_RC_L3, RC_L3_of_ucCdist⟩

/-! ## RHP at Level 3 -/

/-- Robust Hyperproperties Preservation at Level 3.

    For all adversaries A, the simulator construction Sim(A) is admissibility-
    preserving and robust compilation holds at L3. -/
def RHPL3 {hon out leak sim_if view : Type} (ε : ℝ≥0∞)
    (π : hon → T (out ⊕ leak))
    (F : hon → T (out ⊕ sim_if))
    (Sim : SimConstruction T leak sim_if view) : Prop :=
  Sim.admPreserving ∧
  ∀ (A : leak → T view),
    RobustCompilationL3 ε
      (fun a => π a >>= UCMonadBase.ucMapSum pure A)
      (fun a => F a >>= UCMonadBase.ucMapSum pure (Sim A))

/-! ## UCEmulatesAlgL3 ↔ RHPL3 -/

/-- UCEmulatesAlgL3 → RHPL3: UC gives ucCdist ≤ ε, then RC_L3_of_ucCdist lifts. -/
theorem RHPL3_of_UCEmulatesAlgL3
    {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    {π : hon → T (out ⊕ leak)}
    {F : hon → T (out ⊕ sim_if)}
    {Sim : SimConstruction T leak sim_if view}
    (h : UCEmulatesAlgL3 (T := T) ε π F Sim) :
    RHPL3 ε π F Sim :=
  ⟨h.1, fun A => RC_L3_of_ucCdist (h.2 A)⟩

/-- RHPL3 → UCEmulatesAlgL3: specializing RC_L3 contexts recovers ucCdist ≤ ε. -/
theorem UCEmulatesAlgL3_of_RHPL3
    {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    {π : hon → T (out ⊕ leak)}
    {F : hon → T (out ⊕ sim_if)}
    {Sim : SimConstruction T leak sim_if view}
    (h : RHPL3 ε π F Sim) :
    UCEmulatesAlgL3 (T := T) ε π F Sim :=
  ⟨h.1, fun A => ucCdist_of_RC_L3 (h.2 A)⟩

/-- UC ↔ RHP at Level 3 (computational).

    This is the L3 analogue of `UCEmulates_iff_RHP` (RC.lean).
    The key ingredient for the backward direction is `adm_pure`, which
    allows specializing D' = pure when extracting per-distinguisher bounds. -/
theorem UCEmulatesAlgL3_iff_RHPL3
    {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak))
    (F : hon → T (out ⊕ sim_if))
    (Sim : SimConstruction T leak sim_if view) (ε : ℝ≥0∞) :
    UCEmulatesAlgL3 (T := T) ε π F Sim ↔ RHPL3 ε π F Sim :=
  ⟨RHPL3_of_UCEmulatesAlgL3, UCEmulatesAlgL3_of_RHPL3⟩

/-! ## Sequential and Parallel Composition at L3

  Sequential composition is abstract (works for any `UCMonadCompDist T`).
  Parallel composition requires `ucCdist_mapSum_le` which needs a concrete
  bridge through `sdist`; see `CatCrypt.Crypto.RCL3SPComp` for the
  SPComp-specific version `RobustCompilationL3_mapSum_SPComp`. -/

/-- Sequential composition (transitivity) of robust compilation at L3.

    If `f ≈_{ε₁} g` and `g ≈_{ε₂} h`, then `f ≈_{ε₁+ε₂} h`.
    Proof: `RC_L3 ↔ ucCdist` + triangle inequality. -/
theorem RobustCompilationL3_trans {α β : Type} {f g h : α → T β}
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : RobustCompilationL3 ε₁ f g) (h₂ : RobustCompilationL3 ε₂ g h) :
    RobustCompilationL3 (ε₁ + ε₂) f h :=
  RC_L3_of_ucCdist (le_trans (ucCdist_triangle f g h)
    (add_le_add (ucCdist_of_RC_L3 h₁) (ucCdist_of_RC_L3 h₂)))

/-! ## RHP at Level 2

The L1 equivalence `UCEmulates_iff_RHP` and L3 equivalence `UCEmulatesAlgL3_iff_RHPL3`
are proved above. The L2 analog is the missing middle level. Key insight:
`RobustCompilationL3` (restricting to admissible D) serves both L2 and L3 — the
levels differ only in simulator constraints (L3 requires `adm S`, L2 does not). -/

/-- Robust Hyperproperties Preservation at Level 2.

    Like `RHPL3` but without requiring the simulator to be admissible.
    For all adversaries A, there exists a simulator S such that
    robust compilation holds at L3 (i.e., for all admissible distinguishers). -/
def RHPL2 {hon out leak sim_if view : Type} (ε : ℝ≥0∞)
    (π : hon → T (out ⊕ leak))
    (F : hon → T (out ⊕ sim_if)) : Prop :=
  ∀ (A : leak → T view), ∃ (S : sim_if → T view),
    RobustCompilationL3 ε
      (fun a => π a >>= UCMonadBase.ucMapSum pure A)
      (fun a => F a >>= UCMonadBase.ucMapSum pure S)

/-- UCEmulatesL2 → RHPL2: UC gives ucCdist ≤ ε, then RC_L3_of_ucCdist lifts. -/
theorem RHPL2_of_UCEmulatesL2
    {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    {π : hon → T (out ⊕ leak)}
    {F : hon → T (out ⊕ sim_if)}
    (h : UCEmulatesL2 (T := T) (view := view) ε π F) :
    RHPL2 (view := view) ε π F := by
  intro A
  obtain ⟨S, hS⟩ := h A
  exact ⟨S, RC_L3_of_ucCdist hS⟩

/-- RHPL2 → UCEmulatesL2: specializing RC_L3 contexts recovers ucCdist ≤ ε. -/
theorem UCEmulatesL2_of_RHPL2
    {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    {π : hon → T (out ⊕ leak)}
    {F : hon → T (out ⊕ sim_if)}
    (h : RHPL2 (T := T) (view := view) ε π F) :
    UCEmulatesL2 (T := T) (view := view) ε π F := by
  intro A
  obtain ⟨S, hS⟩ := h A
  exact ⟨S, ucCdist_of_RC_L3 hS⟩

/-- UC ↔ RHP at Level 2 (computational distinguishers).

    This is the L2 analogue of `UCEmulates_iff_RHP` (L1) and
    `UCEmulatesAlgL3_iff_RHPL3` (L3), completing the picture at all three levels. -/
theorem UCEmulatesL2_iff_RHPL2
    {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak))
    (F : hon → T (out ⊕ sim_if)) (ε : ℝ≥0∞) :
    UCEmulatesL2 (T := T) (view := view) ε π F ↔
    RHPL2 (T := T) (view := view) ε π F :=
  ⟨RHPL2_of_UCEmulatesL2, UCEmulatesL2_of_RHPL2⟩

/-- Level hierarchy bridge: RHPL3 implies RHPL2.

    Since RHPL3 quantifies over a fixed admissibility-preserving simulator
    construction, we can forget the admissibility constraint to get RHPL2. -/
theorem RHPL2_of_RHPL3
    {hon out leak sim_if view : Type} {ε : ℝ≥0∞}
    {π : hon → T (out ⊕ leak)}
    {F : hon → T (out ⊕ sim_if)}
    {Sim : SimConstruction T leak sim_if view}
    (h : RHPL3 ε π F Sim) :
    RHPL2 (T := T) (view := view) ε π F :=
  fun A => ⟨Sim A, h.2 A⟩

/-! ## Parallel Composition at L3 (Abstract) -/

/-- Abstract parallel composition of `RobustCompilationL3`.

    If `f₁ ≈_{ε₁} f₂` and `g₁ ≈_{ε₂} g₂` at Level 3, then
    `mapSum f₁ g₁ ≈_{max(ε₁,ε₂)} mapSum f₂ g₂` at Level 3.

    The `SPComp` instance is `RobustCompilationL3_mapSum_SPComp` (`RCL3SPComp.lean`). -/
theorem RobustCompilationL3_mapSum {α₁ β₁ α₂ β₂ : Type}
    {ε₁ ε₂ : ℝ≥0∞}
    {f₁ f₂ : α₁ → T β₁} {g₁ g₂ : α₂ → T β₂}
    (h₁ : RobustCompilationL3 ε₁ f₁ f₂)
    (h₂ : RobustCompilationL3 ε₂ g₁ g₂) :
    RobustCompilationL3 (ε₁ ⊔ ε₂)
      (UCMonadBase.ucMapSum f₁ g₁) (UCMonadBase.ucMapSum f₂ g₂) :=
  RC_L3_of_ucCdist (ucCdist_mapSum_le _ _ _ _
    (ucCdist_of_RC_L3 h₁) (ucCdist_of_RC_L3 h₂))

end CatCrypt.Crypto
