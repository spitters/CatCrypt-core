/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SDist
import CatCryptCore.Crypto.UC
import CatCryptCore.Crypto.Advantage
import CatCryptCore.Relational.Rules

/-!
# EasyCrypt Semantic Bridge

This file bridges EasyCrypt-style reasoning (pRHL judgments, advantage bounds)
and CatCrypt's UC security framework (sdist, UCEmulates).

## Main results

### Semantic Chain: pRHL → sdist → UC

* `pRHL_to_UCEmulates` — pRHL equality → UCEmulates at ε = 0
* `sdist_to_UCEmulates` — sdist bound → UCEmulates

### Module Refinement

* `ModuleRefines_comp_right` — Post-composition preserves refinement
* `ModuleRefines_to_UCEmulates` — Module refinement → UCEmulates
* `module_hybrid_bound` — n-step hybrid argument
-/

namespace CatCrypt.Crypto.EasyCryptBridge

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open scoped ENNReal

/-! ## pRHL Vocabulary -/

/-- EasyCrypt-style naming for the pRHL judgment. -/
abbrev pRHL {α β : Type*} (Φ : RPre) (c₁ : SPComp α) (c₂ : SPComp β)
    (Ψ : RPost α β) : Prop :=
  rHoare Φ c₁ c₂ Ψ

/-! ## Semantic Chain: pRHL → sdist → UC -/

/-- pRHL with equality pre/postconditions implies zero advantage for all distinguishers. -/
theorem pRHL_eq_implies_advantage_zero {α : Type*}
    (G₀ G₁ : SPComp α) (h : pRHL eqPre G₀ G₁ eqPost)
    (A : α → SPComp Bool) : AdvantageA G₀ G₁ A = 0 :=
  advantage_zero_of_rHoare G₀ G₁ h A

/-- The lifted eqPost relation equals `Eq` (via Prod.ext). -/
private theorem lifted_eqPost_eq' {β : Type*} :
    (fun (p₁ : β × Heap) (p₂ : β × Heap) => eqPost p₁.1 p₁.2 p₂.1 p₂.2) = Eq := by
  funext p₁ p₂
  simp only [eqPost, eq_iff_iff]
  exact ⟨fun ⟨ha, hh⟩ => Prod.ext ha hh, fun h => ⟨congr_arg Prod.fst h, congr_arg Prod.snd h⟩⟩

/-- pRHL equality at all inputs gives pointwise program equality. -/
theorem pRHL_eq_implies_prog_eq {hon β : Type*}
    (π F : hon → SPComp β)
    (h : ∀ (a : hon), rHoare eqPre (π a) (F a) eqPost) :
    π = F := by
  funext a h₀
  have h_lift := h a h₀ h₀ rfl
  rw [lifted_eqPost_eq'] at h_lift
  exact liftR_eq_implies_eq h_lift

/-- pRHL equality → UCEmulates at ε = 0 (SPComp UC). A trivial same-interface lift
(pRHL equality gives `π = F`, then `UCEmulates_refl`), so simulator = adversary.
(composition plumbing) -/
theorem pRHL_to_UCEmulates {hon out leak view : Type*}
    (π F : hon → SPComp (out ⊕ leak))
    (h : ∀ (a : hon), rHoare eqPre (π a) (F a) eqPost) :
    UCEmulates 0 ⟨hon, out, leak, leak, view⟩ π F := by
  have h_eq : π = F := pRHL_eq_implies_prog_eq π F h
  rw [h_eq]
  exact UCEmulates_refl F

/-- sdist bound → UCEmulates, same interface, via `UCEmulates_of_sdist`.
(composition plumbing) -/
theorem sdist_to_UCEmulates {hon out leak view : Type*}
    (π F : hon → SPComp (out ⊕ leak)) (ε : ℝ≥0∞)
    (h : sdist π F ≤ ε) :
    UCEmulates ε ⟨hon, out, leak, leak, view⟩ π F :=
  UCEmulates_of_sdist ε π F h

/-- IsPure computations with bounded advantage have bounded sdist. -/
theorem sdist_of_isPure_advantage {α : Type*}
    (f g : Unit → SPComp α) (ε : ℝ≥0∞)
    (hf : SPComp.IsPure (f ())) (hg : SPComp.IsPure (g ()))
    (h : ∀ (A : α → SPComp Bool), AdvantageA (f ()) (g ()) A ≤ ε) :
    sdist f g ≤ ε :=
  sdist_of_isPure_advantageA (fun _ => hf) (fun _ => hg) (fun () D => h D)

/-- sdist bound → UCEmulates, same interface, via `UCEmulates_of_sdist`.
(composition plumbing) -/
theorem isPure_advantage_to_UCEmulates {hon out leak view : Type*}
    (π F : hon → SPComp (out ⊕ leak)) (ε : ℝ≥0∞)
    (h : sdist π F ≤ ε) :
    UCEmulates ε ⟨hon, out, leak, leak, view⟩ π F :=
  UCEmulates_of_sdist ε π F h

/-! ## Module Refinement -/

/-- Two SPComp families (modules) are within sdist ε of each other. -/
def ModuleRefines {α β : Type*} (ε : ℝ≥0∞) (M₁ M₂ : α → SPComp β) : Prop :=
  sdist M₁ M₂ ≤ ε

theorem ModuleRefines_refl {α β : Type*} (M : α → SPComp β) :
    ModuleRefines 0 M M := by
  simp [ModuleRefines, sdist_self]

theorem ModuleRefines_sym {α β : Type*} {M₁ M₂ : α → SPComp β} {ε : ℝ≥0∞}
    (h : ModuleRefines ε M₁ M₂) : ModuleRefines ε M₂ M₁ := by
  simp only [ModuleRefines] at *; rwa [sdist_sym]

theorem ModuleRefines_trans {α β : Type*}
    {M₁ M₂ M₃ : α → SPComp β} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : ModuleRefines ε₁ M₁ M₂) (h₂ : ModuleRefines ε₂ M₂ M₃) :
    ModuleRefines (ε₁ + ε₂) M₁ M₃ :=
  le_trans (sdist_triangle M₁ M₂ M₃) (add_le_add h₁ h₂)

theorem ModuleRefines_mono {α β : Type*}
    {M₁ M₂ : α → SPComp β} {ε₁ ε₂ : ℝ≥0∞}
    (h : ModuleRefines ε₁ M₁ M₂) (hle : ε₁ ≤ ε₂) :
    ModuleRefines ε₂ M₁ M₂ :=
  le_trans h hle

/-- Post-composition preserves module refinement (right PPL). -/
theorem ModuleRefines_comp_right {α β γ : Type*}
    {M₁ M₂ : α → SPComp β} {ε : ℝ≥0∞}
    (h : ModuleRefines ε M₁ M₂) (k : β → SPComp γ) :
    ModuleRefines ε (fun a => SPComp.bind (M₁ a) k)
                    (fun a => SPComp.bind (M₂ a) k) :=
  le_trans (sdist_comp_right M₁ M₂ k) h

/-- Pre-composition with shared prefix preserves refinement (left PPL). -/
theorem ModuleRefines_comp_left {α β γ : Type*}
    (f : α → SPComp β) {g₁ g₂ : β → SPComp γ} {ε : ℝ≥0∞}
    (h : ModuleRefines ε g₁ g₂) :
    ModuleRefines ε (fun a => SPComp.bind (f a) g₁)
                    (fun a => SPComp.bind (f a) g₂) :=
  le_trans (sdist_comp_left f g₁ g₂) h

/-- Module refinement (an sdist bound) → UCEmulates, same interface, via
`UCEmulates_of_sdist`. (composition plumbing) -/
theorem ModuleRefines_to_UCEmulates {hon out leak view : Type*}
    {π F : hon → SPComp (out ⊕ leak)} {ε : ℝ≥0∞}
    (h : ModuleRefines ε π F) :
    UCEmulates ε ⟨hon, out, leak, leak, view⟩ π F :=
  UCEmulates_of_sdist ε π F h

/-- Compose two module-refinement (sdist) steps into a UCEmulates bound, same
interface. (composition plumbing) -/
theorem ModuleRefines_chain {hon out leak view : Type*}
    {π G F : hon → SPComp (out ⊕ leak)} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : ModuleRefines ε₁ π G) (h₂ : ModuleRefines ε₂ G F) :
    UCEmulates (ε₁ + ε₂) ⟨hon, out, leak, leak, view⟩ π F :=
  ModuleRefines_to_UCEmulates (ModuleRefines_trans h₁ h₂)

/-! ## Pointwise Equality Bridge -/

/-- If two computations are pointwise equal, their sdist is 0. -/
theorem sdist_zero_of_eq {α β : Type*}
    (f g : α → SPComp β) (h : ∀ (a : α), f a = g a) :
    sdist f g = 0 := by
  rw [show f = g from funext h, sdist_self]

/-- pRHL at all inputs → ModuleRefines at 0. -/
theorem pRHL_to_ModuleRefines {hon β : Type*}
    (π F : hon → SPComp β)
    (h : ∀ (a : hon), rHoare eqPre (π a) (F a) eqPost) :
    ModuleRefines 0 π F := by
  simp only [ModuleRefines]
  rw [pRHL_eq_implies_prog_eq π F h, sdist_self]

/-! ## Hybrid Argument Support -/

/-- n-step hybrid argument at the module level:
    if each adjacent pair is within ε, the endpoints are within n * ε. -/
theorem module_hybrid_bound {α β : Type*} (n : ℕ)
    (games : Fin (n + 1) → α → SPComp β) (ε : ℝ≥0∞)
    (h_step : ∀ (i : Fin n),
      ModuleRefines ε (games i.castSucc) (games i.succ)) :
    ModuleRefines (n * ε) (games 0) (games (Fin.last n)) := by
  induction n with
  | zero => simp [ModuleRefines, sdist_self]
  | succ n ih =>
    have h_step' : ∀ (i : Fin n), ModuleRefines ε
        (games (i.castSucc.castSucc)) (games i.succ.castSucc) :=
      fun i => h_step i.castSucc
    have h_ih := ih (fun i => games i.castSucc) h_step'
    have h_last := h_step (Fin.last n)
    calc sdist (games 0) (games (Fin.last (n + 1)))
        ≤ sdist (games 0) (games (Fin.last n).castSucc)
          + sdist (games (Fin.last n).castSucc) (games (Fin.last (n + 1))) :=
          sdist_triangle _ _ _
      _ ≤ ↑n * ε + ε := add_le_add h_ih h_last
      _ = (↑n + 1) * ε := by rw [add_mul, one_mul]
      _ = ↑(n + 1) * ε := by push_cast; ring

end CatCrypt.Crypto.EasyCryptBridge
