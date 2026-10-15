/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad
public import CatCryptCore.Crypto.SDist

/-!
# SPComp Instance of UCMonad

This file provides the concrete `UCMonad SPComp` instance, connecting
the generic typeclass to the existing CatCrypt infrastructure.

## Main results

* `UCMonad SPComp` — the instance
* `mapSumSP` — a UC-free local copy of `mapSum` (keeps this file off the UC layer)

The generic↔concrete bridge lemmas (`generic_UCEmulates_iff_concrete`,
`generic_approxFact_iff_concrete`) need `Crypto.UC`, so they live in
`SPCompUCBridge.lean`.

## Design

The instance fields map directly:
- `ucMapSum` → `mapSum` (from `UC.lean`)
- `ucFail` → `SPComp.fail` (from `Code.lean`)
- `ucSdist` → `sdist` (from `SDist.lean`)
-/

@[expose] public section

namespace UCMonad

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-! ## Re-derive bind_fail_right (private in Affine.lean) -/

theorem spcomp_bind_fail {α β : Type} (c : SPComp α) :
    SPComp.bind c (fun _ => (SPComp.fail : SPComp β)) = SPComp.fail := by
  funext h
  simp only [SPComp.bind_def, SPComp.fail]
  show SDistr.bind (c h) (fun _ => SDistr.fail) = SDistr.fail
  simp only [SDistr.bind, SDistr.fail]
  calc PMF.bind (c h) _ = PMF.bind (c h) (fun _ => PMF.pure (none : Option (β × Heap))) := by
        congr 1; funext oa; cases oa <;> rfl
    _ = PMF.pure none := PMF.bind_const _ _

/-! ## Localized `mapSum` (UC-free copy)

`mapSum` lives in `UC.lean`, which this file must NOT depend on: keeping
`SPCompInstance` off the UC layer is what makes the whole `RoundM`/`ITreeN`
substrate built on it UC-free (the compiler-boundary cut). `mapSum` is a pure
`Sum`-parallel-composition, so we keep a local copy here; the proofs mirror
`UC.lean` / `UCFactorization.lean`. -/

noncomputable def mapSumSP {α β γ δ : Type} (f : α → SPComp β) (g : γ → SPComp δ) :
    (α ⊕ γ) → SPComp (β ⊕ δ)
  | .inl a => SPComp.map Sum.inl (f a)
  | .inr c => SPComp.map Sum.inr (g c)

@[simp] theorem mapSumSP_inl {α β γ δ : Type} (f : α → SPComp β) (g : γ → SPComp δ) (a : α) :
    mapSumSP f g (.inl a) = SPComp.map Sum.inl (f a) := rfl

@[simp] theorem mapSumSP_inr {α β γ δ : Type} (f : α → SPComp β) (g : γ → SPComp δ) (c : γ) :
    mapSumSP f g (.inr c) = SPComp.map Sum.inr (g c) := rfl

@[simp] theorem mapSumSP_pure_left {α β γ : Type} (g : β → SPComp γ) (a : α) :
    mapSumSP SPComp.pure g (.inl a) = SPComp.pure (.inl a) := by
  simp [mapSumSP, SPComp.map, SPComp.pure_bind]

@[simp] theorem mapSumSP_pure_right {α β γ : Type} (f : α → SPComp β) (c : γ) :
    mapSumSP f SPComp.pure (.inr c) = SPComp.pure (.inr c) := by
  simp [mapSumSP, SPComp.map, SPComp.pure_bind]

theorem mapSumSP_pure_pure {α β : Type} :
    mapSumSP (SPComp.pure (α := α)) (SPComp.pure (α := β)) = SPComp.pure := by
  funext x; cases x <;> simp

theorem mapSumSP_pure_kleisli_comp {α β γ δ : Type}
    (f : β → SPComp γ) (g : γ → SPComp δ) :
    (fun x : α ⊕ β => SPComp.bind (mapSumSP SPComp.pure f x) (mapSumSP SPComp.pure g))
    = mapSumSP SPComp.pure (fun b => SPComp.bind (f b) g) := by
  funext x; rcases x with a | b
  · simp
  · simp only [mapSumSP_inr, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- UC-free copy of `RC.sdist_mapSum_le` for `mapSumSP`. Since `mapSumSP` is
    definitionally `mapSum`, this also closes goals stated with `mapSum`, letting
    the ITreeN multi-session layer stay off the `RC`/UC layer. Proof mirrors
    `RC.sdist_mapSum_le`. -/
theorem sdist_mapSumSP_le {α₁ α₂ β₁ β₂ : Type}
    (f₁ f₂ : α₁ → SPComp α₂) (g₁ g₂ : β₁ → SPComp β₂)
    {ε₁ ε₂ : ℝ≥0∞} (hf : sdist f₁ f₂ ≤ ε₁) (hg : sdist g₁ g₂ ≤ ε₂) :
    sdist (mapSumSP f₁ g₁) (mapSumSP f₂ g₂) ≤ ε₁ ⊔ ε₂ := by
  refine iSup_le fun D => iSup_le fun x => iSup_le fun h₀ => ?_
  rcases x with a | c
  · simp only [mapSumSP_inl, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    exact le_sup_of_le_left (sdist_le_of_forall hf _ _ _)
  · simp only [mapSumSP_inr, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    exact le_sup_of_le_right (sdist_le_of_forall hg _ _ _)

/-! ## The UCMonad instance for SPComp -/

noncomputable instance : UCMonad SPComp where
  ucMapSum := @mapSumSP
  ucMapSum_inl := fun f g a => by simp [mapSumSP, SPComp.map]
  ucMapSum_inr := fun f g c => by simp [mapSumSP, SPComp.map]
  ucMapSum_pure_pure := mapSumSP_pure_pure
  ucMapSum_pure_kleisli := fun f g =>
    mapSumSP_pure_kleisli_comp f g
  ucFail := SPComp.fail
  ucBind_fail := fun c => spcomp_bind_fail c
  ucSdist := @sdist
  ucSdist_self := sdist_self
  ucSdist_sym := sdist_sym
  ucSdist_triangle := sdist_triangle
  ucSdist_comp_right := sdist_comp_right
  ucSdist_comp_left := sdist_comp_left

/-! ## UCPure instance for SPComp -/

/-- `SPComp.IsPure` satisfies the `UCPure` interface. -/
instance : UCPure SPComp where
  isPure := SPComp.IsPure
  isPure_pure := SPComp.pure_isPure
  isPure_bind := fun _ _ hc hf => SPComp.bind_isPure hc hf
  isPure_comm := fun c d k hc => SPComp.isPure_bind_comm_left c d k hc

end UCMonad
