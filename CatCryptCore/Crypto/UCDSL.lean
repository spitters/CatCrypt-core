/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.UC
import CatCryptCore.Crypto.UCMonad.SPCompInstance
import CatCryptCore.Crypto.UCComposition
import CatCryptCore.Crypto.UCAlg

/-!
# Enhanced UC DSL (v2)

Extended notation and proof combinators for the UC factorization framework,
eliminating boilerplate in UC proofs.

## Component A: Protocol definition helpers

* `UCProtocol.ofGame` — wrap a game into UC protocol (the `.inr` boilerplate)
* `UCSpec.ofGame` — standard UC spec for game-to-game reductions

## Component B: One-shot UC proof combinators

* `UCEmulates_of_isPure_advantage` — computational UC from IsPure + advantage bound
* `UCEmulates_of_game_eq` — perfect UC from program equality
* `UCEmulates_of_game_sdist` — sdist at game level implies UC

## Component C: Game-hop chaining

* `sdist_game_hop₂` — 2-step game hop
* `sdist_game_hop₃` — 3-step game hop

## Component D: Mixed Trans instances

* `Trans` for exact followed by approximate
* `Trans` for approximate followed by exact

## Component E: Algebraic UC combinators

* `UCEmulatesAlg` composition tracking simulators
* `Trans` instance for algebraic calc-style proofs
-/

namespace CatCrypt.Crypto.UCDSL

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCAlg
open scoped ENNReal

/-! ## Component A: Protocol Definition Helpers -/

/-- Wrap a game into UC protocol form.

    Eliminates the repetitive `.inr` wrapping pattern found in every `*_UC.lean` file.
    The game output goes through the `.inr` (leak/adversary) channel, while the
    honest output channel `.inl` carries `Unit`. -/
noncomputable def UCProtocol.ofGame {hon leak : Type}
    (G : hon → SPComp leak) : hon → SPComp (Unit ⊕ leak) :=
  fun x => SPComp.bind (G x) (fun o => SPComp.pure (.inr o))

/-- Standard UC specification for game-to-game reductions.

    When reducing game G_real to G_ideal with the same leak type,
    the UC spec has `out = Unit` and `leak = sim_if`. -/
abbrev UCSpec.ofGame (hon leak : Type) (V : Type) : UCSpec :=
  ⟨hon, Unit, leak, leak, V⟩

/-! ## Component B: One-Shot UC Proof Combinators -/

/-- Computational UC emulation from IsPure + advantage bound.

    This is the most common pattern in UC proofs:
    1. Both games are IsPure (built from sample/pure)
    2. The advantage is bounded by ε
    3. sdist_isPure_le reduces sdist to advantage
    4. sdist_comp_right handles the .inr wrapping
    5. UCEmulates_of_sdist gives UC security

    **Before** (PRF_UC.lean, ~25 lines of IsPure proofs + sdist helper + UC theorem):
    ```
    theorem prf_uc_secure ... := by
      apply UCEmulates_of_sdist
      exact le_trans (sdist_comp_right _ _ _) (prf_sdist F ε hAdv)
    ```
    **After** (single application):
    ```
    exact UCEmulates_of_isPure_advantage hPure_r hPure_i hAdv
    ``` -/
theorem UCEmulates_of_isPure_advantage {hon leak V : Type} {ε : ℝ≥0∞}
    {G_real G_ideal : hon → SPComp leak}
    (hPure_r : ∀ x, SPComp.IsPure (G_real x))
    (hPure_i : ∀ x, SPComp.IsPure (G_ideal x))
    (hAdv : ∀ (D : leak → SPComp Bool) (x : hon),
      absDiff (prTrue (SPComp.bind (G_real x) D) Heap.empty)
              (prTrue (SPComp.bind (G_ideal x) D) Heap.empty) ≤ ε) :
    UCEmulates ε (UCSpec.ofGame hon leak V)
      (UCProtocol.ofGame G_real) (UCProtocol.ofGame G_ideal) := by
  apply UCEmulates_of_sdist
  apply le_trans (sdist_comp_right _ _ _)
  exact sdist_isPure_le hPure_r hPure_i hAdv

/-- Perfect UC emulation from program equality.

    When the real and ideal games are extensionally equal, UC emulation
    holds with ε = 0. This covers the OTP pattern.

    **Before** (OTP_UC.lean):
    ```
    apply UCEmulates_of_sdist
    rw [otpReal_eq_otpIdeal]
    exact le_of_eq (sdist_self _)
    ```
    **After:**
    ```
    exact UCEmulates_of_game_eq otpReal_eq_otpIdeal
    ``` -/
theorem UCEmulates_of_game_eq {hon leak V : Type}
    {G_real G_ideal : hon → SPComp leak}
    (h : G_real = G_ideal) :
    UCEmulates 0 (UCSpec.ofGame hon leak V)
      (UCProtocol.ofGame G_real) (UCProtocol.ofGame G_ideal) := by
  apply UCEmulates_of_sdist
  have : UCProtocol.ofGame G_real = UCProtocol.ofGame G_ideal := by
    unfold UCProtocol.ofGame; rw [h]
  rw [this]
  exact le_of_eq (sdist_self _)

/-- UC emulation from sdist bound at the game level.

    When `sdist G_real G_ideal ≤ ε`, UC emulation holds.
    The `.inr` wrapping is handled automatically via `sdist_comp_right`. -/
theorem UCEmulates_of_game_sdist {hon leak V : Type} {ε : ℝ≥0∞}
    {G_real G_ideal : hon → SPComp leak}
    (h : sdist G_real G_ideal ≤ ε) :
    UCEmulates ε (UCSpec.ofGame hon leak V)
      (UCProtocol.ofGame G_real) (UCProtocol.ofGame G_ideal) := by
  apply UCEmulates_of_sdist
  exact le_trans (sdist_comp_right _ _ _) h

/-- Variant of `UCEmulates_of_isPure_advantage` using `AdvantageA`.

    Takes advantage bounds in the form `AdvantageA (G_real x) (G_ideal x) D ≤ ε`
    that appears directly in most security definitions. -/
theorem UCEmulates_of_isPure_advantageA {hon leak V : Type} {ε : ℝ≥0∞}
    {G_real G_ideal : hon → SPComp leak}
    (hPure_r : ∀ x, SPComp.IsPure (G_real x))
    (hPure_i : ∀ x, SPComp.IsPure (G_ideal x))
    (hAdv : ∀ x (D : leak → SPComp Bool), AdvantageA (G_real x) (G_ideal x) D ≤ ε) :
    UCEmulates ε (UCSpec.ofGame hon leak V)
      (UCProtocol.ofGame G_real) (UCProtocol.ofGame G_ideal) := by
  apply UCEmulates_of_sdist
  apply le_trans (sdist_comp_right _ _ _)
  apply sdist_isPure_le hPure_r hPure_i
  intro D x; exact hAdv x D

/-! ## Component C: Game-Hop Chaining -/

/-- 2-step game hop (covers HKDF_UC pattern).

    If `sdist G₀ G₁ ≤ ε₁` and `sdist G₁ G₂ ≤ ε₂`,
    then `sdist G₀ G₂ ≤ ε₁ + ε₂`. -/
theorem sdist_game_hop₂ {α β : Type} {ε₁ ε₂ : ℝ≥0∞}
    {G₀ G₁ G₂ : α → SPComp β}
    (h₁ : sdist G₀ G₁ ≤ ε₁) (h₂ : sdist G₁ G₂ ≤ ε₂) :
    sdist G₀ G₂ ≤ ε₁ + ε₂ :=
  le_trans (sdist_triangle G₀ G₁ G₂) (add_le_add h₁ h₂)

/-- 3-step game hop (covers CascadePRF_UC pattern).

    If `sdist Gᵢ Gᵢ₊₁ ≤ εᵢ` for i = 0, 1, 2, then
    `sdist G₀ G₃ ≤ ε₁ + ε₂ + ε₃`. -/
theorem sdist_game_hop₃ {α β : Type} {ε₁ ε₂ ε₃ : ℝ≥0∞}
    {G₀ G₁ G₂ G₃ : α → SPComp β}
    (h₁ : sdist G₀ G₁ ≤ ε₁) (h₂ : sdist G₁ G₂ ≤ ε₂) (h₃ : sdist G₂ G₃ ≤ ε₃) :
    sdist G₀ G₃ ≤ ε₁ + ε₂ + ε₃ := by
  calc sdist G₀ G₃ ≤ sdist G₀ G₂ + sdist G₂ G₃ := sdist_triangle G₀ G₂ G₃
    _ ≤ (ε₁ + ε₂) + ε₃ := add_le_add (sdist_game_hop₂ h₁ h₂) h₃

/-- 4-step game hop (covers Cryptobox compositional decomposition).

    If `sdist Gᵢ Gᵢ₊₁ ≤ εᵢ` for i = 0, 1, 2, 3, then
    `sdist G₀ G₄ ≤ ε₁ + ε₂ + ε₃ + ε₄`. -/
theorem sdist_game_hop₄ {α β : Type} {ε₁ ε₂ ε₃ ε₄ : ℝ≥0∞}
    {G₀ G₁ G₂ G₃ G₄ : α → SPComp β}
    (h₁ : sdist G₀ G₁ ≤ ε₁) (h₂ : sdist G₁ G₂ ≤ ε₂)
    (h₃ : sdist G₂ G₃ ≤ ε₃) (h₄ : sdist G₃ G₄ ≤ ε₄) :
    sdist G₀ G₄ ≤ ε₁ + ε₂ + ε₃ + ε₄ := by
  calc sdist G₀ G₄ ≤ sdist G₀ G₃ + sdist G₃ G₄ := sdist_triangle G₀ G₃ G₄
    _ ≤ (ε₁ + ε₂ + ε₃) + ε₄ := add_le_add (sdist_game_hop₃ h₁ h₂ h₃) h₄

/-- UC emulation via 2-step game hop.

    Chains two game hops at the UC level. -/
theorem UCEmulates_game_hop₂ {hon leak V : Type} {ε₁ ε₂ : ℝ≥0∞}
    {G₀ G₁ G₂ : hon → SPComp leak}
    (h₁ : sdist G₀ G₁ ≤ ε₁) (h₂ : sdist G₁ G₂ ≤ ε₂) :
    UCEmulates (ε₁ + ε₂) (UCSpec.ofGame hon leak V)
      (UCProtocol.ofGame G₀) (UCProtocol.ofGame G₂) :=
  UCEmulates_of_game_sdist (sdist_game_hop₂ h₁ h₂)

/-! ## Component E: Algebraic UC Combinators -/

section AlgebraicUC

/-- Notation for algebraic UC emulation. -/
scoped notation:50 π " ⟶ₐ[" ε ", " Sim "] " F => UCEmulatesAlg ε _ π F Sim

/-- Composition of algebraic UC emulations tracking simulators.

    If `π₁ ⟶ₐ[ε₁, Sim₁] π₂` and `π₂ ⟶ₐ[ε₂, Sim₂] π₃`,
    then `π₁ ⟶ₐ[ε₁ + ε₂, Sim₂ ∘ Sim₁] π₃`. -/
theorem uc_alg_comp {hon out leak view : Type} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ π₂ π₃ : hon → SPComp (out ⊕ leak)}
    {Sim₁ Sim₂ : SimConstruction ⟨hon, out, leak, leak, view⟩}
    (h₁ : UCEmulatesAlg ε₁ ⟨hon, out, leak, leak, view⟩ π₁ π₂ Sim₁)
    (h₂ : UCEmulatesAlg ε₂ ⟨hon, out, leak, leak, view⟩ π₂ π₃ Sim₂) :
    UCEmulatesAlg (ε₁ + ε₂) ⟨hon, out, leak, leak, view⟩ π₁ π₃ (Sim₂ ∘ Sim₁) :=
  UCEmulatesAlg.trans h₁ h₂

/-- Algebraic UC from sdist with identity simulator. -/
theorem uc_alg_of_sdist {hon out leak view : Type} {ε : ℝ≥0∞}
    {G_real G_ideal : hon → SPComp (out ⊕ leak)}
    (h : sdist G_real G_ideal ≤ ε) :
    UCEmulatesAlg ε ⟨hon, out, leak, leak, view⟩ G_real G_ideal SimConstruction.id :=
  UCEmulatesAlg_of_sdist ε G_real G_ideal h

/-- Trans instance for algebraic UC calc-style proofs. -/
instance ucEmulatesAlg_trans_inst
    {hon out leak view : Type}
    {ε₁ ε₂ : ℝ≥0∞}
    {Sim₁ Sim₂ : SimConstruction ⟨hon, out, leak, leak, view⟩} :
    Trans (fun (π₁ π₂ : hon → SPComp (out ⊕ leak)) =>
            UCEmulatesAlg ε₁ ⟨hon, out, leak, leak, view⟩ π₁ π₂ Sim₁)
          (fun (π₂ π₃ : hon → SPComp (out ⊕ leak)) =>
            UCEmulatesAlg ε₂ ⟨hon, out, leak, leak, view⟩ π₂ π₃ Sim₂)
          (fun (π₁ π₃ : hon → SPComp (out ⊕ leak)) =>
            UCEmulatesAlg (ε₁ + ε₂) ⟨hon, out, leak, leak, view⟩ π₁ π₃ (Sim₂ ∘ Sim₁)) where
  trans := UCEmulatesAlg.trans

end AlgebraicUC

/-! ## Utility: ofGame distributes over function application -/

@[simp]
theorem UCProtocol.ofGame_apply {hon leak : Type} (G : hon → SPComp leak) (x : hon) :
    UCProtocol.ofGame G x = SPComp.bind (G x) (fun o => SPComp.pure (.inr o)) := rfl

/-- `UCSpec.ofGame` expands to the expected anonymous constructor. -/
@[simp]
theorem UCSpec.ofGame_eq {hon leak V : Type} :
    UCSpec.ofGame hon leak V = ⟨hon, Unit, leak, leak, V⟩ := rfl

end CatCrypt.Crypto.UCDSL
