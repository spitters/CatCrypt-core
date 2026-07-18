/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SDist
import CatCryptCore.Category.KlSPComp

set_option autoImplicit false

/-!
# Universal Composability (UC) Security

This file defines UC security at Level 1 (information-theoretic): no complexity bounds.

## Main definitions

* `UCSpec` — specification of UC interfaces (honest, output, leak, sim_if, view)
* `mapSum` — parallel composition on `Sum` (= tensor in `KlSPComp`)
* `realWorld`, `idealWorld` — real and ideal world executions
* `UCEmulates` — UC emulation with statistical error ε
* `UCEmulatesPerfect` — perfect UC emulation (ε = 0)

## Main results

* `mapSum_pure_left` — `mapSum pure g (.inl a) = pure (.inl a)`
* `UCEmulates_of_sdist` — same-interface: `sdist ≤ ε → UCEmulates ε`
* `UCEmulates_of_dummy` — dummy adversary sufficiency
* `UCEmulates_trans` — transitivity (same-interface, via simulator chaining)

## UC vs sdist

UC emulation (Canetti-style `∀ A ∃ S`) is strictly weaker than `sdist ≤ ε`.
The implication `sdist ≤ ε → UCEmulates ε` holds (take `S = A`), but the
reverse is false because the simulator can transform the leak channel. (The
robust-hyperproperty (RHP) equivalence is developed separately.)

## Sub-SMC structure (same-interface case)

When `leak = sim_if` (same adversary interface), UC emulation inherits the
sub-SMC structure from sdist:
* `UCEmulates_refl` — identity: any protocol emulates itself
* `UCEmulates_trans` — composition: simulator chaining gives additive bounds
* Tensor: follows from `sdist_mapSum_le` via `UCEmulates_of_sdist`

For the general case (different interfaces), the categorical structure is
richer — it involves a 2-categorical notion where simulators are 2-cells.

## Concurrent UC (forthcoming)

This file provides single-shot, non-interactive UC emulation. The concurrent
(reactive) layer — `UCEmulatesConcurrent*` over the ITreeN interaction-tree
monad, with the Kantorovich-distance and stateful variants — will be included in
core in a forthcoming revision; it currently lives in the parent development
under `CatCrypt/Crypto/UCMonad/`.
-/

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob

open scoped ENNReal

/-! ## UC Specification -/

/-- A UC specification bundles the types of the various interfaces.

    - `hon` : honest input interface
    - `out` : honest output interface
    - `leak` : adversary interface (real world leakage)
    - `sim_if` : simulator interface (ideal world)
    - `view` : adversary/simulator observable output -/
structure UCSpec where
  hon    : Type*
  out    : Type*
  leak   : Type*
  sim_if : Type*
  view   : Type*

/-! ## Parallel Composition on Sum -/

/-- Concrete parallel composition on `Sum` (= tensor `⊗` in `KlSPComp`).
    Applies `f` on `.inl` and `g` on `.inr`. -/
noncomputable def mapSum {α β γ δ : Type*} (f : α → SPComp β) (g : γ → SPComp δ) :
    (α ⊕ γ) → SPComp (β ⊕ δ)
  | .inl a => SPComp.map Sum.inl (f a)
  | .inr c => SPComp.map Sum.inr (g c)

@[simp]
theorem mapSum_inl {α β γ δ : Type*} (f : α → SPComp β) (g : γ → SPComp δ) (a : α) :
    mapSum f g (.inl a) = SPComp.map Sum.inl (f a) := rfl

@[simp]
theorem mapSum_inr {α β γ δ : Type*} (f : α → SPComp β) (g : γ → SPComp δ) (c : γ) :
    mapSum f g (.inr c) = SPComp.map Sum.inr (g c) := rfl

@[simp] theorem mapSum_pure_left {α β γ : Type*} (g : β → SPComp γ) (a : α) :
    mapSum SPComp.pure g (.inl a) = SPComp.pure (.inl a) := by
  simp [mapSum, SPComp.map, SPComp.pure_bind]

@[simp] theorem mapSum_pure_right {α β γ : Type*} (f : α → SPComp β) (c : γ) :
    mapSum f SPComp.pure (.inr c) = SPComp.pure (.inr c) := by
  simp [mapSum, SPComp.map, SPComp.pure_bind]

/-- `mapSum pure pure = pure` (identity on Sum). -/
@[simp] theorem mapSum_pure_pure {α β : Type*} :
    mapSum (SPComp.pure (α := α)) (SPComp.pure (α := β)) = SPComp.pure := by
  funext x; rcases x with a | b
  · exact mapSum_pure_left _ a
  · exact mapSum_pure_right _ b

/-- `mapSum f g` equals the KlSPComp tensor product `wkR f ≫ wkL g`. -/
theorem mapSum_eq_tensorHom {α₁ α₂ β₁ β₂ : Type}
    (f : α₁ → SPComp α₂) (g : β₁ → SPComp β₂) :
    mapSum f g = fun x => SPComp.bind (KlSPComp.wkR f β₁ x)
      (KlSPComp.wkL α₂ g) := by
  funext x; rcases x with a | c
  · simp [mapSum, KlSPComp.wkR, KlSPComp.wkL, SPComp.map, SPComp.bind_assoc]
  · simp [mapSum, KlSPComp.wkR, KlSPComp.wkL, SPComp.map]

/-! ## Real and Ideal Worlds -/

/-- Real world: `Z ∘ₖ (id ⊕ A) ∘ₖ π`. -/
noncomputable def realWorld (spec : UCSpec)
    (π : spec.hon → SPComp (spec.out ⊕ spec.leak))
    (A : spec.leak → SPComp spec.view)
    (Z : (spec.out ⊕ spec.view) → SPComp Bool) :
    spec.hon → SPComp Bool :=
  fun a => SPComp.bind (SPComp.bind (π a) (mapSum SPComp.pure A)) Z

/-- Ideal world: `Z ∘ₖ (id ⊕ S) ∘ₖ F`. -/
noncomputable def idealWorld (spec : UCSpec)
    (F : spec.hon → SPComp (spec.out ⊕ spec.sim_if))
    (S : spec.sim_if → SPComp spec.view)
    (Z : (spec.out ⊕ spec.view) → SPComp Bool) :
    spec.hon → SPComp Bool :=
  fun a => SPComp.bind (SPComp.bind (F a) (mapSum SPComp.pure S)) Z

/-! ## UC Emulation -/

/-- Protocol `π` UC-emulates ideal functionality `F` with statistical error `ε`.

    For ALL adversaries A, there EXISTS a simulator S such that
    the sdist of the post-adversary views is ≤ ε.
    The environment Z is absorbed into sdist's distinguisher supremum. -/
def UCEmulates (ε : ℝ≥0∞) (spec : UCSpec)
    (π : spec.hon → SPComp (spec.out ⊕ spec.leak))
    (F : spec.hon → SPComp (spec.out ⊕ spec.sim_if)) : Prop :=
  ∀ (A : spec.leak → SPComp spec.view),
    ∃ (S : spec.sim_if → SPComp spec.view),
      sdist (fun a => SPComp.bind (π a) (mapSum SPComp.pure A))
            (fun a => SPComp.bind (F a) (mapSum SPComp.pure S)) ≤ ε

/-- Perfect UC emulation: ε = 0. -/
def UCEmulatesPerfect (spec : UCSpec)
    (π : spec.hon → SPComp (spec.out ⊕ spec.leak))
    (F : spec.hon → SPComp (spec.out ⊕ spec.sim_if)) : Prop :=
  UCEmulates 0 spec π F

/-! ## Basic Theorems -/

/-- Same-interface UC: if `sdist π F ≤ ε`, then `UCEmulates ε` with `S = A`.
    When `leak = sim_if`, the simulator is just the adversary itself. -/
theorem UCEmulates_of_sdist {out leak : Type*} (ε : ℝ≥0∞)
    {view : Type*} {hon : Type*}
    (π F : hon → SPComp (out ⊕ leak))
    (h : sdist π F ≤ ε) :
    UCEmulates ε ⟨hon, out, leak, leak, view⟩ π F := by
  intro A
  exact ⟨A, le_trans (sdist_comp_right π F (mapSum SPComp.pure A)) h⟩

/-- Monotonicity: UC emulation with tighter bound implies looser bound. -/
@[grind →] theorem UCEmulates_mono {spec : UCSpec}
    {π : spec.hon → SPComp (spec.out ⊕ spec.leak)}
    {F : spec.hon → SPComp (spec.out ⊕ spec.sim_if)} {ε₁ ε₂ : ℝ≥0∞}
    (h : UCEmulates ε₁ spec π F) (hle : ε₁ ≤ ε₂) :
    UCEmulates ε₂ spec π F := by
  intro A
  obtain ⟨S, hS⟩ := h A
  exact ⟨S, le_trans hS hle⟩

/-- Dummy adversary sufficiency (same-interface case: `view = leak`).

    If UC holds against the identity adversary, it holds against ALL adversaries.
    The key idea: given adversary A, absorb it into the distinguisher. -/
theorem UCEmulates_of_dummy {hon out leak : Type*} (ε : ℝ≥0∞)
    (π F : hon → SPComp (out ⊕ leak))
    (h : sdist π F ≤ ε) :
    ∀ (view : Type*) (A : leak → SPComp view),
      ∃ (S : leak → SPComp view),
        sdist (fun a => SPComp.bind (π a) (mapSum SPComp.pure A))
              (fun a => SPComp.bind (F a) (mapSum SPComp.pure S)) ≤ ε := by
  intro view A
  -- Take S = A (same adversary as simulator)
  exact ⟨A, le_trans (sdist_comp_right π F (mapSum SPComp.pure A)) h⟩

/-- Reflexivity: any protocol UC-emulates itself perfectly (same-interface). -/
theorem UCEmulates_refl {hon out leak view : Type*}
    (π : hon → SPComp (out ⊕ leak)) :
    UCEmulates 0 ⟨hon, out, leak, leak, view⟩ π π := by
  intro A
  exact ⟨A, by simp [sdist_self]⟩

/-- Transitivity of UC emulation (same-interface case).

    Given adversary A, chain simulators: h₁ gives S₁ for A, h₂ gives S₂ for S₁.
    The triangle inequality on sdist gives the additive bound.
    This is the composition property for the UC sub-SMC. -/
theorem UCEmulates_trans {hon out leak view : Type*} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ π₂ π₃ : hon → SPComp (out ⊕ leak)}
    (h₁ : UCEmulates ε₁ ⟨hon, out, leak, leak, view⟩ π₁ π₂)
    (h₂ : UCEmulates ε₂ ⟨hon, out, leak, leak, view⟩ π₂ π₃) :
    UCEmulates (ε₁ + ε₂) ⟨hon, out, leak, leak, view⟩ π₁ π₃ := by
  intro A
  obtain ⟨S₁, hS₁⟩ := h₁ A
  obtain ⟨S₂, hS₂⟩ := h₂ S₁
  exact ⟨S₂, le_trans (sdist_triangle _ _ _) (add_le_add hS₁ hS₂)⟩

/-! ## Heterogeneous Transitivity -/

/-- Heterogeneous transitivity: compose UC bounds across different leak types.
    Given π₁ ──UC(ε₁)──▶ π₂ (leak₁ → leak₂) and π₂ ──UC(ε₂)──▶ π₃ (leak₂ → sim_if),
    we get π₁ ──UC(ε₁+ε₂)──▶ π₃ (leak₁ → sim_if). The middle type leak₂ is consumed. -/
theorem UCEmulates_trans_hetero {hon out leak₁ leak₂ sim_if view : Type*} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ : hon → SPComp (out ⊕ leak₁)}
    {π₂ : hon → SPComp (out ⊕ leak₂)}
    {π₃ : hon → SPComp (out ⊕ sim_if)}
    (h₁ : UCEmulates ε₁ ⟨hon, out, leak₁, leak₂, view⟩ π₁ π₂)
    (h₂ : UCEmulates ε₂ ⟨hon, out, leak₂, sim_if, view⟩ π₂ π₃) :
    UCEmulates (ε₁ + ε₂) ⟨hon, out, leak₁, sim_if, view⟩ π₁ π₃ := by
  intro A
  obtain ⟨S₁, hS₁⟩ := h₁ A
  obtain ⟨S₂, hS₂⟩ := h₂ S₁
  exact ⟨S₂, le_trans (sdist_triangle _ _ _) (add_le_add hS₁ hS₂)⟩

/-- Heterogeneous transitivity for 3-step pipelines. -/
theorem UCEmulates_trans_hetero₃ {hon out l₁ l₂ l₃ sim view : Type*}
    {ε₁ ε₂ ε₃ : ℝ≥0∞}
    {π₁ : hon → SPComp (out ⊕ l₁)}
    {π₂ : hon → SPComp (out ⊕ l₂)}
    {π₃ : hon → SPComp (out ⊕ l₃)}
    {π₄ : hon → SPComp (out ⊕ sim)}
    (h₁ : UCEmulates ε₁ ⟨hon, out, l₁, l₂, view⟩ π₁ π₂)
    (h₂ : UCEmulates ε₂ ⟨hon, out, l₂, l₃, view⟩ π₂ π₃)
    (h₃ : UCEmulates ε₃ ⟨hon, out, l₃, sim, view⟩ π₃ π₄) :
    UCEmulates (ε₁ + ε₂ + ε₃) ⟨hon, out, l₁, sim, view⟩ π₁ π₄ :=
  add_assoc ε₁ ε₂ ε₃ ▸ UCEmulates_trans_hetero h₁ (UCEmulates_trans_hetero h₂ h₃)

/-! ## Oracle-Game UC Emulation -/

/-- UC emulation for oracle-based (interactive) games.

    Many cryptographic security definitions give the adversary oracle access
    to a set of operations (e.g., encryption, decryption, key generation).
    The game constructs the oracles and hands them to the adversary, who
    produces a distinguishing bit.

    `GameUCEmulates ε G_real G_ideal` says that no adversary can distinguish
    the real game from the ideal game with advantage greater than `ε`.

    This generalizes `UCEmulates` to the reactive/oracle setting where
    the adversary interacts via multiple adaptive queries rather than
    receiving a single output. -/
def GameUCEmulates (ε : ℝ≥0∞) {OracleIf : Type*}
    (G_real G_ideal : (OracleIf → SPComp Bool) → SPComp Bool) : Prop :=
  ∀ (A : OracleIf → SPComp Bool), Advantage (G_real A) (G_ideal A) ≤ ε

/-- Reflexivity: any game trivially emulates itself. -/
theorem GameUCEmulates_refl {OracleIf : Type*}
    (G : (OracleIf → SPComp Bool) → SPComp Bool) :
    GameUCEmulates 0 G G := by
  intro A; exact le_of_eq (Advantage_self _)

/-- Monotonicity: tighter bound implies looser bound. -/
theorem GameUCEmulates_mono {OracleIf : Type*}
    {G_real G_ideal : (OracleIf → SPComp Bool) → SPComp Bool}
    {ε₁ ε₂ : ℝ≥0∞} (h : GameUCEmulates ε₁ G_real G_ideal) (hle : ε₁ ≤ ε₂) :
    GameUCEmulates ε₂ G_real G_ideal :=
  fun A => le_trans (h A) hle

/-- Transitivity via triangle inequality. -/
theorem GameUCEmulates_trans {OracleIf : Type*}
    {G₁ G₂ G₃ : (OracleIf → SPComp Bool) → SPComp Bool}
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : GameUCEmulates ε₁ G₁ G₂)
    (h₂ : GameUCEmulates ε₂ G₂ G₃) :
    GameUCEmulates (ε₁ + ε₂) G₁ G₃ :=
  fun A => le_trans (advantage_triangle _ _ _) (add_le_add (h₁ A) (h₂ A))

/-- Symmetry: swapping real and ideal preserves the bound. -/
theorem GameUCEmulates_sym {OracleIf : Type*}
    {G_real G_ideal : (OracleIf → SPComp Bool) → SPComp Bool}
    {ε : ℝ≥0∞} (h : GameUCEmulates ε G_real G_ideal) :
    GameUCEmulates ε G_ideal G_real :=
  fun A => (Advantage_sym _ _) ▸ (h A)

end CatCrypt.Crypto
