/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.UC

/-!
# Algebraic UC Emulation: Explicit Simulator Constructions

This file upgrades existential UC emulation (`∀ A, ∃ S, ...`) to a version
that records the simulator as an explicit function `A ↦ Sim(A)` of the
adversary. Most concrete UC proofs already build `S` as a concrete
function of `A`, so this is the natural formulation; `UCEmulatesAlg.forget`
re-extracts the existential `UCEmulates` when needed.

## Main definitions

* `SimConstruction` — function `(leak → SPComp view) → (sim_if → SPComp view)`
  mapping each adversary to a simulator.
* `UCEmulatesAlg` — UC emulation with the explicit `SimConstruction` witness.

## Main results

* `UCEmulatesAlg.forget` — algebraic implies existential (`→ UCEmulates`)
* `UCEmulatesAlg_of_sdist` — from sdist (same-interface, `Sim = id`)
* `UCEmulatesAlg.refl` — reflexivity (`Sim = id`)
* `UCEmulatesAlg.trans` — same-interface transitivity (composition of `Sim`)
* `UCEmulatesAlg.trans_general` — general transitivity through different interfaces
* `SimConstruction.id_comp`, `comp_id`, `comp_assoc` — composition laws (all `rfl`)

## Composition structure

`SimConstruction.id` and `SimConstruction.comp` give a unit and an
associative composition with both unit laws — these hold by `rfl` because
`SimConstruction` is just a function and `comp` is function composition.
Errors compose additively under the `ℝ≥0∞` grading via `UCEmulatesAlg.trans`.

The earlier framing of this structure as an "approximate algebraic weak
factorization system" was rhetorical: the small-object argument and
genuine algebra structure of an AWFS are not used here — the content is
"explicit simulator + sdist bound, composed pointwise".
-/

namespace CatCrypt.Crypto.UCAlg

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## Simulator Construction -/

/-- A simulator construction: a function from adversaries to simulators.

    Given an adversary `A : leak → SPComp view`, produces a simulator
    `Sim(A) : sim_if → SPComp view`. -/
def SimConstruction (spec : UCSpec) : Type :=
  (spec.leak → SPComp spec.view) → (spec.sim_if → SPComp spec.view)

/-- Identity simulator construction (same-interface: `leak = sim_if`).
    The adversary IS the simulator. -/
def SimConstruction.id {hon out leak view : Type} :
    SimConstruction ⟨hon, out, leak, leak, view⟩ :=
  _root_.id

/-- Composition of simulator constructions.
    `comp Sim₁ Sim₂` first applies `Sim₁` then `Sim₂`: given adversary `A`,
    the composed simulator is `Sim₂(Sim₁(A))`. -/
def SimConstruction.comp {hon out leak₁ leak₂ leak₃ view : Type}
    (Sim₁ : SimConstruction ⟨hon, out, leak₁, leak₂, view⟩)
    (Sim₂ : SimConstruction ⟨hon, out, leak₂, leak₃, view⟩) :
    SimConstruction ⟨hon, out, leak₁, leak₃, view⟩ :=
  Sim₂ ∘ Sim₁

/-! ## Composition Laws (all `rfl` since `SimConstruction` is a function) -/

@[simp]
theorem SimConstruction.id_comp {hon out leak₁ leak₂ view : Type}
    (Sim : SimConstruction ⟨hon, out, leak₁, leak₂, view⟩) :
    SimConstruction.comp SimConstruction.id Sim = Sim := rfl

@[simp]
theorem SimConstruction.comp_id {hon out leak₁ leak₂ view : Type}
    (Sim : SimConstruction ⟨hon, out, leak₁, leak₂, view⟩) :
    SimConstruction.comp Sim SimConstruction.id = Sim := rfl

theorem SimConstruction.comp_assoc {hon out leak₁ leak₂ leak₃ leak₄ view : Type}
    (Sim₁ : SimConstruction ⟨hon, out, leak₁, leak₂, view⟩)
    (Sim₂ : SimConstruction ⟨hon, out, leak₂, leak₃, view⟩)
    (Sim₃ : SimConstruction ⟨hon, out, leak₃, leak₄, view⟩) :
    SimConstruction.comp (SimConstruction.comp Sim₁ Sim₂) Sim₃ =
    SimConstruction.comp Sim₁ (SimConstruction.comp Sim₂ Sim₃) := rfl

/-! ## Algebraic UC Emulation -/

/-- UC emulation with explicit simulator construction.

    Upgrades the existential `∀ A, ∃ S` in `UCEmulates` to a concrete
    witness `Sim : A ↦ S(A)` satisfying the sdist bound uniformly. -/
def UCEmulatesAlg (ε : ℝ≥0∞) (spec : UCSpec)
    (π : spec.hon → SPComp (spec.out ⊕ spec.leak))
    (F : spec.hon → SPComp (spec.out ⊕ spec.sim_if))
    (Sim : SimConstruction spec) : Prop :=
  ∀ (A : spec.leak → SPComp spec.view),
    sdist (fun a => SPComp.bind (π a) (mapSum SPComp.pure A))
          (fun a => SPComp.bind (F a) (mapSum SPComp.pure (Sim A))) ≤ ε

/-! ## Basic Properties -/

/-- Forget the algebraic witness: `UCEmulatesAlg → UCEmulates`. -/
theorem UCEmulatesAlg.forget {ε : ℝ≥0∞} {spec : UCSpec}
    {π : spec.hon → SPComp (spec.out ⊕ spec.leak)}
    {F : spec.hon → SPComp (spec.out ⊕ spec.sim_if)}
    {Sim : SimConstruction spec}
    (h : UCEmulatesAlg ε spec π F Sim) :
    UCEmulates ε spec π F :=
  fun A => ⟨Sim A, h A⟩

/-- Monotonicity: tighter bound implies looser bound (same simulator). -/
theorem UCEmulatesAlg.mono {ε₁ ε₂ : ℝ≥0∞} {spec : UCSpec}
    {π : spec.hon → SPComp (spec.out ⊕ spec.leak)}
    {F : spec.hon → SPComp (spec.out ⊕ spec.sim_if)}
    {Sim : SimConstruction spec}
    (h : UCEmulatesAlg ε₁ spec π F Sim) (hle : ε₁ ≤ ε₂) :
    UCEmulatesAlg ε₂ spec π F Sim :=
  fun A => le_trans (h A) hle

/-! ## Same-Interface Constructions -/

/-- Reflexivity: any protocol emulates itself with `Sim = id`. -/
theorem UCEmulatesAlg.refl {hon out leak view : Type}
    (π : hon → SPComp (out ⊕ leak)) :
    UCEmulatesAlg 0 ⟨hon, out, leak, leak, view⟩ π π SimConstruction.id :=
  fun _ => le_of_eq (sdist_self _)

/-- From sdist: same-interface with `Sim = id`. -/
theorem UCEmulatesAlg_of_sdist {out leak : Type} (ε : ℝ≥0∞)
    {view : Type} {hon : Type}
    (π F : hon → SPComp (out ⊕ leak))
    (h : sdist π F ≤ ε) :
    UCEmulatesAlg ε ⟨hon, out, leak, leak, view⟩ π F SimConstruction.id :=
  fun A => le_trans (sdist_comp_right π F (mapSum SPComp.pure A)) h

/-! ## Transitivity (Simulator Composition) -/

/-- Same-interface transitivity via simulator composition.
    Errors compose additively: `ε₁ + ε₂`. -/
theorem UCEmulatesAlg.trans {hon out leak view : Type} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ π₂ π₃ : hon → SPComp (out ⊕ leak)}
    {Sim₁ Sim₂ : SimConstruction ⟨hon, out, leak, leak, view⟩}
    (h₁ : UCEmulatesAlg ε₁ ⟨hon, out, leak, leak, view⟩ π₁ π₂ Sim₁)
    (h₂ : UCEmulatesAlg ε₂ ⟨hon, out, leak, leak, view⟩ π₂ π₃ Sim₂) :
    UCEmulatesAlg (ε₁ + ε₂) ⟨hon, out, leak, leak, view⟩ π₁ π₃ (Sim₂ ∘ Sim₁) :=
  fun A => le_trans (sdist_triangle _ _ _) (add_le_add (h₁ A) (h₂ (Sim₁ A)))

/-- General transitivity through different interface types.

    Chains `π₁ ⟶^{Sim₁} π₂ ⟶^{Sim₂} π₃` via `SimConstruction.comp`. -/
theorem UCEmulatesAlg.trans_general
    {hon out leak₁ leak₂ leak₃ view : Type} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ : hon → SPComp (out ⊕ leak₁)}
    {π₂ : hon → SPComp (out ⊕ leak₂)}
    {π₃ : hon → SPComp (out ⊕ leak₃)}
    {Sim₁ : SimConstruction ⟨hon, out, leak₁, leak₂, view⟩}
    {Sim₂ : SimConstruction ⟨hon, out, leak₂, leak₃, view⟩}
    (h₁ : UCEmulatesAlg ε₁ ⟨hon, out, leak₁, leak₂, view⟩ π₁ π₂ Sim₁)
    (h₂ : UCEmulatesAlg ε₂ ⟨hon, out, leak₂, leak₃, view⟩ π₂ π₃ Sim₂) :
    UCEmulatesAlg (ε₁ + ε₂) ⟨hon, out, leak₁, leak₃, view⟩ π₁ π₃
      (SimConstruction.comp Sim₁ Sim₂) :=
  fun A => le_trans (sdist_triangle _ _ _) (add_le_add (h₁ A) (h₂ (Sim₁ A)))

end CatCrypt.Crypto.UCAlg
