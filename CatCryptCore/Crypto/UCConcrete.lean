/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCDSL
public import CatCryptCore.Crypto.UCComposition

@[expose] public section
set_option autoImplicit false

/-!
# Concrete UC Emulation

UC emulation in which the environment's distinguishing advantage is bounded by
a function of the adversary and of the environment, in the style of concrete
security (EasyCrypt, EasyUC: Canetti, Stoughton, Varia, CSF 2019). A bound
such as `bound A Z = DDH_Advantage (B A Z)`, for an explicit reduction `B`,
constrains every adversary and environment individually.

`UCEmulates ε` bounds `sdist`, the supremum over all distinguishers. The
concrete form is pointwise: `UCEmulatesC` with a constant bound is exactly
`UCEmulates` (`UCEmulatesC_const_iff`), so statistical results embed.

## Main definitions

* `Env` — an environment for a Kleisli morphism `α → SPComp β`: an input, an
  initial heap and a distinguisher.
* `Env.gap` — the distinguishing gap of one environment between two morphisms.
* `DistC f g bound` — the gap of every environment `Z` is at most `bound Z`.
* `UCEmulatesC spec π F bound` — for every adversary `A` there is a simulator
  `S` whose ideal run is `bound A`-close to the real run with `A`.
* `UCEmulatesCSim spec π F sim bound` — the same with the simulator given by
  an explicit map `sim` from adversaries to simulators.
* `fixHeap`, `PureGame`, `GameAdvBoundC`, `gameUCBound`, `UCFromGameC` — the
  route from a concrete game bound to concrete UC emulation.

## Main results

* `DistC_const_iff`, `UCEmulatesC_const_iff`, `UCEmulatesCSim_const_iff` —
  constant bounds are the numeric notions `sdist ≤ ε`, `UCEmulates ε`,
  `UCEmulatesAlg ε`.
* `DistC.comp_right`, `DistC.comp_left`, `DistC.mapSum`, `DistC.triangle` —
  post-processing, pre-composition, parallel composition, game hops, with
  the reductions visible in the bound.
* `UCEmulatesCSim.trans` — transitivity, the second bound evaluated at the
  simulator produced by the first.
* `UCEmulatesCSim_compile`, `UCEmulatesCSim_par` — concrete subroutine and
  parallel composition.
* `DistC_of_isPure_advantageA`, `ucFromGameC_of_pure_adv` — concrete game
  bound to concrete UC emulation, with `S = A`.

## Simulator quantifier

`UCEmulatesCSim` records the simulator as a map `sim` of the adversary; it is
the primary form because transitivity evaluates the second bound at the
simulator of the first (`b₂ (sim₁ A)`), which cannot be named when the
simulator is only existential. `UCEmulatesC` keeps Canetti's `∀ A ∃ S` shape
and is equivalent to `∃ sim, UCEmulatesCSim … sim …`
(`UCEmulatesC_iff_exists_sim`).

## Environment

The environment is the triple of input, initial heap and distinguisher, the
three quantities over which `sdist` takes its supremum. A bound may depend on
all three: the IND-CPA reduction to DDH embeds the environment's messages.
-/

namespace CatCrypt.Crypto.UCConcrete

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCDSL CatCrypt.Crypto.UCComposition
open scoped ENNReal

/-! ## Environments and concrete distance -/

/-- An environment for Kleisli morphisms `α → SPComp β`: it chooses the input,
    the initial heap, and the distinguisher run on the output. -/
structure Env (α β : Type*) where
  /-- Input fed to the morphism. -/
  input : α
  /-- Initial heap. -/
  heap : Heap
  /-- Distinguisher run on the output. -/
  dist : β → SPComp Bool

/-- Distinguishing gap of the environment `Z` between `f` and `g`. -/
noncomputable def Env.gap {α β : Type*} (f g : α → SPComp β) (Z : Env α β) : ℝ≥0∞ :=
  absDiff (prTrue (SPComp.bind (f Z.input) Z.dist) Z.heap)
    (prTrue (SPComp.bind (g Z.input) Z.dist) Z.heap)

/-- Concrete distance: every environment `Z` distinguishes `f` from `g` with
    gap at most `bound Z`. -/
def DistC {α β : Type*} (f g : α → SPComp β) (bound : Env α β → ℝ≥0∞) : Prop :=
  ∀ Z, Env.gap f g Z ≤ bound Z

/-- The environment `Z` precomposed with the post-processing `k`: same input
    and heap, distinguisher `k` followed by `Z.dist`. This is the reduction
    used by the right post-processing lemma. -/
noncomputable def Env.postcomp {α β γ : Type*} (k : β → SPComp γ) (Z : Env α γ) : Env α β :=
  ⟨Z.input, Z.heap, fun b => SPComp.bind (k b) Z.dist⟩

/-- A constant concrete bound is the numeric bound `sdist f g ≤ ε`. -/
theorem DistC_const_iff {α β : Type*} {f g : α → SPComp β} {ε : ℝ≥0∞} :
    DistC f g (fun _ => ε) ↔ sdist f g ≤ ε := by
  constructor
  · intro h
    apply iSup_le; intro D; apply iSup_le; intro a; apply iSup_le; intro h₀
    exact h ⟨a, h₀, D⟩
  · intro h Z
    refine le_trans ?_ h
    unfold sdist Env.gap
    exact le_iSup₂_of_le Z.dist Z.input
      (le_iSup_of_le (f := fun h₀ => absDiff (prTrue (SPComp.bind (f Z.input) Z.dist) h₀)
        (prTrue (SPComp.bind (g Z.input) Z.dist) h₀)) Z.heap le_rfl)

/-- Monotonicity in the bound. -/
theorem DistC.mono {α β : Type*} {f g : α → SPComp β} {b₁ b₂ : Env α β → ℝ≥0∞}
    (h : DistC f g b₁) (hle : ∀ Z, b₁ Z ≤ b₂ Z) : DistC f g b₂ :=
  fun Z => le_trans (h Z) (hle Z)

/-- Every morphism has concrete distance `0` from itself. -/
theorem DistC.refl {α β : Type*} (f : α → SPComp β) : DistC f f (fun _ => 0) :=
  fun Z => by simp [Env.gap]

/-- Symmetry. -/
theorem DistC.symm {α β : Type*} {f g : α → SPComp β} {b : Env α β → ℝ≥0∞}
    (h : DistC f g b) : DistC g f b :=
  fun Z => by simpa [Env.gap, absDiff_comm] using h Z

/-- Game hop: concrete bounds add pointwise. -/
theorem DistC.triangle {α β : Type*} {f g k : α → SPComp β} {b₁ b₂ : Env α β → ℝ≥0∞}
    (h₁ : DistC f g b₁) (h₂ : DistC g k b₂) : DistC f k (fun Z => b₁ Z + b₂ Z) :=
  fun Z => le_trans (absDiff_triangle _ _ _) (add_le_add (h₁ Z) (h₂ Z))

/-- Right post-processing: running `k` after both morphisms is bounded by the
    bound of the environment that runs `k` inside its distinguisher. -/
theorem DistC.comp_right {α β γ : Type*} {f₁ f₂ : α → SPComp β}
    {b : Env α β → ℝ≥0∞} (k : β → SPComp γ) (h : DistC f₁ f₂ b) :
    DistC (fun a => SPComp.bind (f₁ a) k) (fun a => SPComp.bind (f₂ a) k)
      (fun Z => b (Env.postcomp k Z)) := by
  intro Z
  have := h (Env.postcomp k Z)
  simpa [Env.gap, Env.postcomp, SPComp.bind_assoc] using this

/-- Pre-composition with a common computation: the bound is the supremum of
    the continuation bound over intermediate values and heaps, with the
    distinguisher unchanged. -/
theorem DistC.comp_left {α β γ : Type*} (f : α → SPComp β) {g₁ g₂ : β → SPComp γ}
    {b : Env β γ → ℝ≥0∞} (h : DistC g₁ g₂ b) :
    DistC (fun a => SPComp.bind (f a) g₁) (fun a => SPComp.bind (f a) g₂)
      (fun Z => ⨆ (y : β) (h' : Heap), b ⟨y, h', Z.dist⟩) := by
  intro Z
  simp only [Env.gap, SPComp.bind_assoc]
  apply absDiff_prTrue_bind_le (f Z.input) _ _ Z.heap
  · intro y h'
    exact le_add_of_absDiff_le
      (le_trans (h ⟨y, h', Z.dist⟩) (le_iSup₂_of_le y h' le_rfl))
  · intro y h'
    exact le_add_of_absDiff_le (by
      rw [absDiff_comm]
      exact le_trans (h ⟨y, h', Z.dist⟩) (le_iSup₂_of_le y h' le_rfl))

/-- Case split of a bound on sum-typed environments: an environment on input
    `.inl a` is sent to the left bound with the distinguisher restricted to
    `.inl`, and symmetrically on the right. -/
def Env.sumCase {α₁ α₂ β₁ β₂ : Type*} (b₁ : Env α₁ β₁ → ℝ≥0∞) (b₂ : Env α₂ β₂ → ℝ≥0∞) :
    Env (α₁ ⊕ α₂) (β₁ ⊕ β₂) → ℝ≥0∞
  | ⟨.inl a, h, D⟩ => b₁ ⟨a, h, fun y => D (.inl y)⟩
  | ⟨.inr a, h, D⟩ => b₂ ⟨a, h, fun y => D (.inr y)⟩

/-- Parallel composition on `Sum`: each input activates one component, so the
    bound is the component bound of the activated side. -/
theorem DistC.mapSum {α₁ α₂ β₁ β₂ : Type*} {f₁ g₁ : α₁ → SPComp β₁}
    {f₂ g₂ : α₂ → SPComp β₂} {b₁ : Env α₁ β₁ → ℝ≥0∞} {b₂ : Env α₂ β₂ → ℝ≥0∞}
    (h₁ : DistC f₁ g₁ b₁) (h₂ : DistC f₂ g₂ b₂) :
    DistC (mapSum f₁ f₂) (mapSum g₁ g₂) (Env.sumCase b₁ b₂) := by
  rintro ⟨a | a, h₀, D⟩
  · have := h₁ ⟨a, h₀, fun y => D (.inl y)⟩
    simpa [Env.gap, Env.sumCase, mapSum, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind] using this
  · have := h₂ ⟨a, h₀, fun y => D (.inr y)⟩
    simpa [Env.gap, Env.sumCase, mapSum, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind] using this

/-! ## Concrete UC emulation -/

/-- Concrete UC emulation: for every adversary `A` there is a simulator `S`
    such that every environment `Z` distinguishes the real run of `π` with `A`
    from the ideal run of `F` with `S` with gap at most `bound A Z`. -/
def UCEmulatesC (spec : UCSpec)
    (π : spec.hon → SPComp (spec.out ⊕ spec.leak))
    (F : spec.hon → SPComp (spec.out ⊕ spec.sim_if))
    (bound : (spec.leak → SPComp spec.view) → Env spec.hon (spec.out ⊕ spec.view) → ℝ≥0∞) :
    Prop :=
  ∀ (A : spec.leak → SPComp spec.view),
    ∃ (S : spec.sim_if → SPComp spec.view),
      DistC (fun a => SPComp.bind (π a) (mapSum SPComp.pure A))
        (fun a => SPComp.bind (F a) (mapSum SPComp.pure S)) (bound A)

/-- Concrete UC emulation with the simulator given by the map `sim`. -/
def UCEmulatesCSim (spec : UCSpec)
    (π : spec.hon → SPComp (spec.out ⊕ spec.leak))
    (F : spec.hon → SPComp (spec.out ⊕ spec.sim_if))
    (sim : (spec.leak → SPComp spec.view) → (spec.sim_if → SPComp spec.view))
    (bound : (spec.leak → SPComp spec.view) → Env spec.hon (spec.out ⊕ spec.view) → ℝ≥0∞) :
    Prop :=
  ∀ (A : spec.leak → SPComp spec.view),
    DistC (fun a => SPComp.bind (π a) (mapSum SPComp.pure A))
      (fun a => SPComp.bind (F a) (mapSum SPComp.pure (sim A))) (bound A)

/-- An explicit simulator map yields concrete UC emulation. -/
theorem UCEmulatesCSim.forget {spec : UCSpec}
    {π : spec.hon → SPComp (spec.out ⊕ spec.leak)}
    {F : spec.hon → SPComp (spec.out ⊕ spec.sim_if)}
    {sim : (spec.leak → SPComp spec.view) → (spec.sim_if → SPComp spec.view)}
    {bound : (spec.leak → SPComp spec.view) → Env spec.hon (spec.out ⊕ spec.view) → ℝ≥0∞}
    (h : UCEmulatesCSim spec π F sim bound) : UCEmulatesC spec π F bound :=
  fun A => ⟨sim A, h A⟩

/-- `∀ A ∃ S` is equivalent to the existence of a simulator map. -/
theorem UCEmulatesC_iff_exists_sim {spec : UCSpec}
    {π : spec.hon → SPComp (spec.out ⊕ spec.leak)}
    {F : spec.hon → SPComp (spec.out ⊕ spec.sim_if)}
    {bound : (spec.leak → SPComp spec.view) → Env spec.hon (spec.out ⊕ spec.view) → ℝ≥0∞} :
    UCEmulatesC spec π F bound ↔ ∃ sim, UCEmulatesCSim spec π F sim bound := by
  constructor
  · intro h
    choose sim hsim using h
    exact ⟨sim, hsim⟩
  · rintro ⟨sim, h⟩
    exact h.forget

/-- A constant concrete bound is numeric UC emulation. -/
theorem UCEmulatesC_const_iff {spec : UCSpec}
    {π : spec.hon → SPComp (spec.out ⊕ spec.leak)}
    {F : spec.hon → SPComp (spec.out ⊕ spec.sim_if)} {ε : ℝ≥0∞} :
    UCEmulatesC spec π F (fun _ _ => ε) ↔ UCEmulates ε spec π F := by
  simp only [UCEmulatesC, UCEmulates, DistC_const_iff]

/-- A constant concrete bound with an explicit simulator map is algebraic UC
    emulation. -/
theorem UCEmulatesCSim_const_iff {spec : UCSpec.{0, 0, 0, 0, 0}}
    {π : spec.hon → SPComp (spec.out ⊕ spec.leak)}
    {F : spec.hon → SPComp (spec.out ⊕ spec.sim_if)}
    {sim : UCAlg.SimConstruction spec} {ε : ℝ≥0∞} :
    UCEmulatesCSim spec π F sim (fun _ _ => ε) ↔ UCAlg.UCEmulatesAlg ε spec π F sim := by
  simp only [UCEmulatesCSim, UCAlg.UCEmulatesAlg, DistC_const_iff]

/-- Monotonicity in the bound. -/
theorem UCEmulatesC.mono {spec : UCSpec}
    {π : spec.hon → SPComp (spec.out ⊕ spec.leak)}
    {F : spec.hon → SPComp (spec.out ⊕ spec.sim_if)}
    {b₁ b₂ : (spec.leak → SPComp spec.view) → Env spec.hon (spec.out ⊕ spec.view) → ℝ≥0∞}
    (h : UCEmulatesC spec π F b₁) (hle : ∀ A Z, b₁ A Z ≤ b₂ A Z) :
    UCEmulatesC spec π F b₂ := by
  intro A
  obtain ⟨S, hS⟩ := h A
  exact ⟨S, hS.mono (hle A)⟩

/-- Monotonicity in the bound, simulator map fixed. -/
theorem UCEmulatesCSim.mono {spec : UCSpec}
    {π : spec.hon → SPComp (spec.out ⊕ spec.leak)}
    {F : spec.hon → SPComp (spec.out ⊕ spec.sim_if)}
    {sim : (spec.leak → SPComp spec.view) → (spec.sim_if → SPComp spec.view)}
    {b₁ b₂ : (spec.leak → SPComp spec.view) → Env spec.hon (spec.out ⊕ spec.view) → ℝ≥0∞}
    (h : UCEmulatesCSim spec π F sim b₁) (hle : ∀ A Z, b₁ A Z ≤ b₂ A Z) :
    UCEmulatesCSim spec π F sim b₂ :=
  fun A => (h A).mono (hle A)

/-- Reflexivity with the identity simulator map and bound `0`. -/
theorem UCEmulatesCSim.refl {hon out leak view : Type*}
    (π : hon → SPComp (out ⊕ leak)) :
    UCEmulatesCSim ⟨hon, out, leak, leak, view⟩ π π id (fun _ _ => 0) :=
  fun _ => DistC.refl _

/-- Transitivity: the simulator maps compose, and the second bound is
    evaluated at the simulator produced by the first. -/
theorem UCEmulatesCSim.trans {hon out leak₁ leak₂ leak₃ view : Type*}
    {π₁ : hon → SPComp (out ⊕ leak₁)} {π₂ : hon → SPComp (out ⊕ leak₂)}
    {π₃ : hon → SPComp (out ⊕ leak₃)}
    {sim₁ : (leak₁ → SPComp view) → (leak₂ → SPComp view)}
    {sim₂ : (leak₂ → SPComp view) → (leak₃ → SPComp view)}
    {b₁ : (leak₁ → SPComp view) → Env hon (out ⊕ view) → ℝ≥0∞}
    {b₂ : (leak₂ → SPComp view) → Env hon (out ⊕ view) → ℝ≥0∞}
    (h₁ : UCEmulatesCSim ⟨hon, out, leak₁, leak₂, view⟩ π₁ π₂ sim₁ b₁)
    (h₂ : UCEmulatesCSim ⟨hon, out, leak₂, leak₃, view⟩ π₂ π₃ sim₂ b₂) :
    UCEmulatesCSim ⟨hon, out, leak₁, leak₃, view⟩ π₁ π₃ (sim₂ ∘ sim₁)
      (fun A Z => b₁ A Z + b₂ (sim₁ A) Z) :=
  fun A => (h₁ A).triangle (h₂ (sim₁ A))

/-- Transitivity of the existential form when the second bound does not
    depend on the adversary. -/
theorem UCEmulatesC.trans {hon out leak₁ leak₂ leak₃ view : Type*}
    {π₁ : hon → SPComp (out ⊕ leak₁)} {π₂ : hon → SPComp (out ⊕ leak₂)}
    {π₃ : hon → SPComp (out ⊕ leak₃)}
    {b₁ : (leak₁ → SPComp view) → Env hon (out ⊕ view) → ℝ≥0∞}
    {b₂ : Env hon (out ⊕ view) → ℝ≥0∞}
    (h₁ : UCEmulatesC ⟨hon, out, leak₁, leak₂, view⟩ π₁ π₂ b₁)
    (h₂ : UCEmulatesC ⟨hon, out, leak₂, leak₃, view⟩ π₂ π₃ (fun _ Z => b₂ Z)) :
    UCEmulatesC ⟨hon, out, leak₁, leak₃, view⟩ π₁ π₃ (fun A Z => b₁ A Z + b₂ Z) := by
  intro A
  obtain ⟨S₁, hS₁⟩ := h₁ A
  obtain ⟨S₂, hS₂⟩ := h₂ S₁
  exact ⟨S₂, hS₁.triangle hS₂⟩

/-- Same interface (composition plumbing): a concrete distance between `π`
    and `F` gives concrete UC emulation with the adversary as simulator; the
    bound runs the adversary inside the environment's distinguisher. -/
theorem UCEmulatesCSim_of_DistC {hon out leak view : Type*}
    {π F : hon → SPComp (out ⊕ leak)} {b : Env hon (out ⊕ leak) → ℝ≥0∞}
    (h : DistC π F b) :
    UCEmulatesCSim ⟨hon, out, leak, leak, view⟩ π F id
      (fun A Z => b (Env.postcomp (mapSum SPComp.pure A) Z)) :=
  fun A => h.comp_right (mapSum SPComp.pure A)

/-! ## Subroutine and parallel composition -/

/-- Concrete subroutine composition: replacing `π` by `F` and `ρ_real` by
    `ρ_ideal` costs the subroutine bound, taken at the intermediate values
    and heaps with the distinguisher restricted to `.inr`, plus the protocol
    bound at the environment that runs `ρ_ideal` inside its distinguisher. -/
theorem DistC_compile {α β γ δ : Type*}
    {π F : α → SPComp (β ⊕ γ)} {ρ_real ρ_ideal : γ → SPComp δ}
    {b₁ : Env α (β ⊕ γ) → ℝ≥0∞} {b₂ : Env γ δ → ℝ≥0∞}
    (hπ : DistC π F b₁) (hρ : DistC ρ_real ρ_ideal b₂) :
    DistC (compile π ρ_real) (compile F ρ_ideal)
      (fun Z => (⨆ (c : γ) (h' : Heap), b₂ ⟨c, h', fun d => Z.dist (.inr d)⟩) +
        b₁ (Env.postcomp (mapSum SPComp.pure ρ_ideal) Z)) := by
  have hsub : DistC (mapSum (SPComp.pure (α := β)) ρ_real) (mapSum SPComp.pure ρ_ideal)
      (Env.sumCase (fun _ => 0) b₂) := (DistC.refl _).mapSum hρ
  have hleft := hsub.comp_left π
  have hright := hπ.comp_right (mapSum SPComp.pure ρ_ideal)
  refine (hleft.triangle hright).mono fun Z => add_le_add ?_ le_rfl
  refine iSup₂_le fun y h' => ?_
  rcases y with b | c
  · exact zero_le
  · exact le_iSup₂_of_le c h' le_rfl

/-- Concrete UC subroutine composition (composition plumbing), same interface
    with the adversary as simulator. -/
theorem UCEmulatesCSim_compile {α β γ δ V : Type*}
    {π F : α → SPComp (β ⊕ γ)} {ρ_real ρ_ideal : γ → SPComp δ}
    {b₁ : Env α (β ⊕ γ) → ℝ≥0∞} {b₂ : Env γ δ → ℝ≥0∞}
    (hπ : DistC π F b₁) (hρ : DistC ρ_real ρ_ideal b₂) :
    UCEmulatesCSim ⟨α, β, δ, δ, V⟩ (compile π ρ_real) (compile F ρ_ideal) id
      (fun A Z =>
        let Z' := Env.postcomp (mapSum SPComp.pure A) Z
        (⨆ (c : γ) (h' : Heap), b₂ ⟨c, h', fun d => Z'.dist (.inr d)⟩) +
          b₁ (Env.postcomp (mapSum SPComp.pure ρ_ideal) Z')) :=
  UCEmulatesCSim_of_DistC (DistC_compile hπ hρ)

/-- Concrete UC parallel composition (composition plumbing): the output of
    `mapSum π₁ π₂` is exposed on the adversary channel, and each environment is
    charged the bound of the component its input activates. -/
theorem UCEmulatesCSim_par {α₁ β₁ α₂ β₂ V : Type*}
    {π₁ F₁ : α₁ → SPComp β₁} {π₂ F₂ : α₂ → SPComp β₂}
    {b₁ : Env α₁ β₁ → ℝ≥0∞} {b₂ : Env α₂ β₂ → ℝ≥0∞}
    (h₁ : DistC π₁ F₁ b₁) (h₂ : DistC π₂ F₂ b₂) :
    UCEmulatesCSim ⟨α₁ ⊕ α₂, Unit, β₁ ⊕ β₂, β₁ ⊕ β₂, V⟩
      (fun x => SPComp.bind (mapSum π₁ π₂ x) (fun o => SPComp.pure (.inr o)))
      (fun x => SPComp.bind (mapSum F₁ F₂ x) (fun o => SPComp.pure (.inr o))) id
      (fun A Z => Env.sumCase b₁ b₂
        (Env.postcomp (fun o => SPComp.pure (Sum.inr o))
          (Env.postcomp (mapSum SPComp.pure A) Z))) :=
  UCEmulatesCSim_of_DistC ((h₁.mapSum h₂).comp_right _)

/-! ## Concrete game route -/

/-- The distinguisher `D` with its initial heap fixed to `h₀`: it ignores the
    heap it is run on. For a heap-independent game `G`, running `D` after `G`
    from `h₀` equals running `fixHeap h₀ D` after `G` from `Heap.empty`. -/
def fixHeap {β : Type*} (h₀ : Heap) (D : β → SPComp Bool) : β → SPComp Bool :=
  fun b _ => D b h₀

/-- Concrete distance from a per-distinguisher advantage bound on
    heap-independent games: the environment `Z` is charged the game bound at
    its input and its distinguisher with the heap fixed to `Z.heap`. -/
theorem DistC_of_isPure_advantageA {α β : Type*} {f g : α → SPComp β}
    {gb : α → (β → SPComp Bool) → ℝ≥0∞}
    (hf : ∀ a, SPComp.IsPure (f a)) (hg : ∀ a, SPComp.IsPure (g a))
    (hAdv : ∀ a D, AdvantageA (f a) (g a) D ≤ gb a D) :
    DistC f g (fun Z => gb Z.input (fixHeap Z.heap Z.dist)) := by
  rintro ⟨a, h₀, D⟩
  obtain ⟨df, hdf⟩ := hf a
  obtain ⟨dg, hdg⟩ := hg a
  have heq_f : prTrue (SPComp.bind (f a) D) h₀ =
      prTrue (SPComp.bind (f a) (fixHeap h₀ D)) Heap.empty := by
    unfold prTrue; congr 1; funext h; congr 1
    rw [isPure_bind_expand hdf D h₀, isPure_bind_expand hdf _ Heap.empty]; rfl
  have heq_g : prTrue (SPComp.bind (g a) D) h₀ =
      prTrue (SPComp.bind (g a) (fixHeap h₀ D)) Heap.empty := by
    unfold prTrue; congr 1; funext h; congr 1
    rw [isPure_bind_expand hdg D h₀, isPure_bind_expand hdg _ Heap.empty]; rfl
  show absDiff _ _ ≤ _
  rw [heq_f, heq_g]
  exact hAdv a (fixHeap h₀ D)

/-- A family of heap-independent games. -/
class PureGame {hon leak : Type*} (G : hon → SPComp leak) : Prop where
  isPure : ∀ x, SPComp.IsPure (G x)

/-- Concrete game bound: the advantage of every distinguisher `D` on input `x`
    is at most `bound x D`, where `bound` is typically the advantage of an
    explicit reduction built from `D` against a primitive.

    `bound` is an explicit index, fixed by the goal. -/
class GameAdvBoundC {hon leak : Type*} (G_real G_ideal : hon → SPComp leak)
    (bound : hon → (leak → SPComp Bool) → ℝ≥0∞) : Prop where
  bound_le : ∀ x (D : leak → SPComp Bool), AdvantageA (G_real x) (G_ideal x) D ≤ bound x D

/-- The distinguisher that the game bound receives from adversary `A` and UC
    environment `Z`: run `A` on the game output, pass its view to `Z.dist` on
    the adversary channel, with the heap fixed to `Z.heap`. -/
noncomputable def envReduction {hon leak V : Type*} (A : leak → SPComp V)
    (Z : Env hon (Unit ⊕ V)) : leak → SPComp Bool :=
  fixHeap Z.heap (fun o => SPComp.bind (A o) (fun v => Z.dist (.inr v)))

/-- UC bound induced by a concrete game bound: the game bound at the
    environment's input and at `envReduction A Z`. -/
noncomputable def gameUCBound {hon leak V : Type*}
    (bound : hon → (leak → SPComp Bool) → ℝ≥0∞) :
    (leak → SPComp V) → Env hon (Unit ⊕ V) → ℝ≥0∞ :=
  fun A Z => bound Z.input (envReduction A Z)

/-- Running a game wrapped by `UCProtocol.ofGame`, then the adversary, then a
    distinguisher, is running the game followed by the adversary and the
    distinguisher on the adversary channel. -/
theorem ofGame_run_eq {hon leak V : Type} (G : hon → SPComp leak) (A : leak → SPComp V)
    (D : Unit ⊕ V → SPComp Bool) (x : hon) :
    SPComp.bind (SPComp.bind (UCProtocol.ofGame G x) (mapSum SPComp.pure A)) D =
      SPComp.bind (G x) (fun o => SPComp.bind (A o) (fun v => D (.inr v))) := by
  simp [UCProtocol.ofGame, mapSum, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- Concrete UC emulation of a game pair from heap-independence and a concrete
    game bound (composition plumbing, simulator `S = A`). -/
theorem UCEmulatesCSim_of_isPure_advantageA {hon leak V : Type}
    {G_real G_ideal : hon → SPComp leak} {bound : hon → (leak → SPComp Bool) → ℝ≥0∞}
    (hPure_r : ∀ x, SPComp.IsPure (G_real x)) (hPure_i : ∀ x, SPComp.IsPure (G_ideal x))
    (hAdv : ∀ x D, AdvantageA (G_real x) (G_ideal x) D ≤ bound x D) :
    UCEmulatesCSim (UCSpec.ofGame hon leak V)
      (UCProtocol.ofGame G_real) (UCProtocol.ofGame G_ideal) id (gameUCBound bound) := by
  intro A Z
  have h := DistC_of_isPure_advantageA hPure_r hPure_i hAdv
    ⟨Z.input, Z.heap, fun o => SPComp.bind (A o) (fun v => Z.dist (.inr v))⟩
  show absDiff
      (prTrue (SPComp.bind (SPComp.bind (UCProtocol.ofGame G_real Z.input)
        (mapSum SPComp.pure A)) Z.dist) Z.heap)
      (prTrue (SPComp.bind (SPComp.bind (UCProtocol.ofGame G_ideal Z.input)
        (mapSum SPComp.pure A)) Z.dist) Z.heap) ≤ _
  rw [ofGame_run_eq, ofGame_run_eq]
  exact h

/-- Concrete UC emulation of `UCProtocol.ofGame G_real` by
    `UCProtocol.ofGame G_ideal` with view type `V`, simulator `S = A`, and the
    bound induced by the game bound `bound`. -/
class UCFromGameC {hon leak : Type} (G_real G_ideal : hon → SPComp leak) (V : Type)
    (bound : hon → (leak → SPComp Bool) → ℝ≥0∞) : Prop where
  uc : UCEmulatesCSim (UCSpec.ofGame hon leak V)
    (UCProtocol.ofGame G_real) (UCProtocol.ofGame G_ideal) id (gameUCBound bound)

/-- Heap-independent games with a concrete game bound give concrete UC
    emulation (composition plumbing). -/
instance ucFromGameC_of_pure_adv {hon leak V : Type}
    {G_real G_ideal : hon → SPComp leak} {bound : hon → (leak → SPComp Bool) → ℝ≥0∞}
    [PureGame G_real] [PureGame G_ideal] [GameAdvBoundC G_real G_ideal bound] :
    UCFromGameC G_real G_ideal V bound :=
  ⟨UCEmulatesCSim_of_isPure_advantageA (PureGame.isPure (G := G_real))
    (PureGame.isPure (G := G_ideal)) GameAdvBoundC.bound_le⟩

end CatCrypt.Crypto.UCConcrete
