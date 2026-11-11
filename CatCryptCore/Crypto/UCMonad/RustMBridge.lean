/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UC
public import CatCryptCore.Crypto.UCMonad.SPCompInstance
public import CatCryptCore.Crypto.UCMonad.Transformers
public import CatCryptCore.Hax.RustM

/-!
# RustM–SPComp Bridge for Hax Extraction

This file provides the `UCMonadMorphism` from `RustM` to `SPComp`, enabling
hax-extracted Rust code (which lives in `RustM`) to be used directly in
CatCrypt's UC security framework.

## Architecture

```
  Hax extraction       This file              UC proofs
  ─────────────       ──────────              ─────────
  RustM α    ──liftRust──→  SPComp α    ──UCMonad──→  security bounds
```

`RustM` is the result monad `Aeneas.Std.RustM` of hax-lean under its root-level name
(`CatCrypt/Hax/RustM.lean`), a deterministic error monad (`.ok | .fail | .div`). Mapping errors to the zero sub-distribution (`SPComp.fail`) gives a canonical
embedding into `SPComp` that preserves the monad structure and is non-expansive.

## Main definitions

* `liftRust` — maps `RustM α → SPComp α`, sending errors to `SPComp.fail`
* `UCMonadMetric RustM` — discrete metric on `RustM` (0 or ⊤)
* `rustToSPComp` — the `UCMonadMorphism RustM SPComp`
* `PanicFree` — predicate witnessing that a `RustM` function never errors
* `liftRust_panicFree` — when panic-free, `liftRust` reduces to `pure`
* `PanicFreeOn` — a `RustM` function returns `.ok` on every argument satisfying a
  precondition; `panicFree_iff_panicFreeOn`, `PanicFreeOn_bind`, `PanicFreeOn_pure`,
  `liftRust_panicFreeOn`

## Design

`RustM` does NOT satisfy `UCMonadAffine` because it has multiple failure modes
(`.fail e` for each `e : Error`, plus `.div`). The affine property requires
`c >>= (fun _ => fail) = fail` for all `c`, but `.fail e >>= f = .fail e`
regardless of `f`, so no single `fail` value works. This is fine: the
`UCMonadMorphism` only requires `UCMonadMetric`, not `UCMonadAffine`.

`ExceptT Error SPComp` is also deliberately avoided because it breaks both the
affine property and the left PPL (see `UCMonad/Transformers.lean`).

Instead, we collapse errors into the zero distribution (`SPComp.fail`), which
is the existing `ucFail` of the `UCMonad SPComp` instance. This makes the
morphism well-behaved and preserves all UC bounds.

## References

* Kammar-McDermott, "Factorisation systems for logical relations" (MFPS 2018)
* CatCrypt UCMonad axioms (UCMonad.lean §1)
-/

@[expose] public section

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto Classical
open scoped ENNReal

namespace UCMonad.RustMBridge

/-! ## Section 1: Lifting RustM to SPComp -/

/-- Lift a `RustM` computation into `SPComp`.

    * `.ok v` becomes `SPComp.pure v`
    * `.fail e` becomes `SPComp.fail` (zero sub-distribution)
    * `.div` becomes `SPComp.fail` (zero sub-distribution)

    This is the canonical embedding: errors are absorbed into sub-probability
    (mass < 1), which is how CatCrypt models failure/abort. -/
noncomputable def liftRust {α : Type} : RustM α → SPComp α
  | .ok v => SPComp.pure v
  | .fail _ => SPComp.fail
  | .div => SPComp.fail

@[simp] theorem liftRust_ok {α : Type} (v : α) :
    liftRust (.ok v) = SPComp.pure v := rfl

@[simp] theorem liftRust_fail {α : Type} (e : Error) :
    liftRust (.fail e : RustM α) = SPComp.fail := rfl

@[simp] theorem liftRust_div {α : Type} :
    liftRust (.div : RustM α) = SPComp.fail := rfl

@[simp] theorem liftRust_pure {α : Type} (a : α) :
    liftRust (pure a : RustM α) = SPComp.pure a := rfl

/-- `liftRust` preserves bind. -/
theorem liftRust_bind {α β : Type} (m : RustM α) (f : α → RustM β) :
    liftRust (m >>= f) = SPComp.bind (liftRust m) (fun a => liftRust (f a)) := by
  cases m with
  | ok v => simp [liftRust, SPComp.pure_bind]
  | fail e => simp [liftRust, SPComp.fail_bind]
  | div => simp [liftRust, SPComp.fail_bind]

/-! ## Section 2: UCMonadMetric for RustM (discrete)

Note: `RustM` gets `UCMonadMetric` but NOT `UCMonadAffine` or `UCMonad`.
Multiple failure modes prevent the affine property. The `UCMonadMorphism`
only requires `UCMonadMetric` on both source and target. -/

/-- Discrete statistical distance on `RustM`: 0 if equal everywhere, ⊤ otherwise. -/
noncomputable def sdistRustM {α β : Type} (f g : α → RustM β) : ℝ≥0∞ :=
  if f = g then 0 else ⊤

theorem sdistRustM_eq {α β : Type} (f g : α → RustM β) :
    sdistRustM f g = if f = g then 0 else ⊤ := rfl

@[simp] theorem sdistRustM_self {α β : Type} (f : α → RustM β) :
    sdistRustM f f = 0 := by rw [sdistRustM_eq]; simp

theorem sdistRustM_sym {α β : Type} (f g : α → RustM β) :
    sdistRustM f g = sdistRustM g f := by
  unfold sdistRustM; grind

theorem sdistRustM_triangle {α β : Type} (f g h : α → RustM β) :
    sdistRustM f h ≤ sdistRustM f g + sdistRustM g h := by
  by_cases hfg : f = g
  · subst hfg; simp [sdistRustM]
  · calc sdistRustM f h ≤ (⊤ : ℝ≥0∞) := le_top
      _ = ⊤ + sdistRustM g h := (top_add _).symm
      _ = sdistRustM f g + sdistRustM g h := by
          unfold sdistRustM; simp_all

theorem sdistRustM_comp_right {α β γ : Type} (f g : α → RustM β) (k : β → RustM γ) :
    sdistRustM (fun a => f a >>= k) (fun a => g a >>= k) ≤ sdistRustM f g := by
  by_cases hfg : f = g
  · subst hfg; simp [sdistRustM]
  · have : sdistRustM f g = ⊤ := by rw [sdistRustM_eq]; simp [hfg]
    simp_all

theorem sdistRustM_comp_left {α β γ : Type} (f : α → RustM β) (g₁ g₂ : β → RustM γ) :
    sdistRustM (fun a => f a >>= g₁) (fun a => f a >>= g₂) ≤ sdistRustM g₁ g₂ := by
  by_cases hg : g₁ = g₂
  · subst hg; simp [sdistRustM]
  · have : sdistRustM g₁ g₂ = ⊤ := by rw [sdistRustM_eq]; simp [hg]
    simp_all

/-- Parallel composition on `Sum` for `RustM`. -/
def mapSumRustM {α β γ δ : Type} (f : α → RustM β) (g : γ → RustM δ) :
    (α ⊕ γ) → RustM (β ⊕ δ)
  | .inl a => RustM.bind (f a) (fun b => .ok (.inl b))
  | .inr c => RustM.bind (g c) (fun d => .ok (.inr d))

theorem mapSumRustM_pure_pure {α β : Type} :
    mapSumRustM (pure : α → RustM α) (pure : β → RustM β) = pure := by
  -- `simp` leaves a residual `RustM.ok _ = pure _`, closed by `rfl`.
  funext x; rcases x with a | b <;> simp [mapSumRustM] <;> rfl

theorem mapSumRustM_pure_kleisli {α β γ δ : Type}
    (f : β → RustM γ) (g : γ → RustM δ) :
    (fun x : α ⊕ β => RustM.bind (mapSumRustM pure f x) (mapSumRustM pure g))
    = mapSumRustM pure (fun b => RustM.bind (f b) g) := by
  funext x; rcases x with a | b
  · simp [mapSumRustM, pure, Pure.pure]
  · simp [mapSumRustM, pure, Pure.pure]
    cases f b <;> simp [mapSumRustM]

/-! ## UCMonadMetric instance for RustM -/

noncomputable instance : UCMonadMetric RustM where
  ucMapSum := @mapSumRustM
  ucMapSum_inl := fun f g a => by
    -- The residual `match` on `f a` is discharged by cases.
    simp [mapSumRustM]; cases f a <;> rfl
  ucMapSum_inr := fun f g c => by
    simp [mapSumRustM]; cases g c <;> rfl
  ucMapSum_pure_pure := mapSumRustM_pure_pure
  ucMapSum_pure_kleisli := fun f g => mapSumRustM_pure_kleisli f g
  ucSdist := @sdistRustM
  ucSdist_self := sdistRustM_self
  ucSdist_sym := sdistRustM_sym
  ucSdist_triangle := sdistRustM_triangle
  ucSdist_comp_right := sdistRustM_comp_right
  ucSdist_comp_left := sdistRustM_comp_left

/-! ## Section 3: UCMonadMorphism from RustM to SPComp -/

/-- The `liftRust` morphism preserves `mapSum`. -/
theorem liftRust_mapSum {α β γ δ : Type}
    (f : α → RustM β) (g : γ → RustM δ) (x : α ⊕ γ) :
    liftRust (UCMonadBase.ucMapSum f g x) =
    UCMonadBase.ucMapSum
      (T := SPComp) (fun a => liftRust (f a)) (fun c => liftRust (g c)) x := by
  show liftRust (mapSumRustM f g x) =
    mapSum (fun a => liftRust (f a)) (fun c => liftRust (g c)) x
  rcases x with a | c
  · simp only [mapSumRustM, mapSum, SPComp.map]
    cases f a <;> simp [liftRust, SPComp.fail_bind, SPComp.pure_bind]
  · simp only [mapSumRustM, mapSum, SPComp.map]
    cases g c <;> simp [liftRust, SPComp.fail_bind, SPComp.pure_bind]

/-- `liftRust` is non-expansive: it doesn't increase statistical distance.

    Since `RustM` has the discrete metric (0 or ⊤), this is trivially true:
    equal functions map to equal functions (distance 0), and ⊤ is an upper bound. -/
theorem liftRust_nonexpansive {α β : Type} (f g : α → RustM β) :
    sdist (fun a => liftRust (f a)) (fun a => liftRust (g a)) ≤
    UCMonadMetric.ucSdist (T := RustM) f g := by
  show sdist (fun a => liftRust (f a)) (fun a => liftRust (g a)) ≤ sdistRustM f g
  rw [sdistRustM_eq]
  split
  case isTrue hfg =>
    have : (fun a => liftRust (f a)) = (fun a => liftRust (g a)) := by
      simp_all
    rw [this, sdist_self]
  case isFalse _ => bound

/-- The `UCMonadMorphism` from `RustM` to `SPComp`.

    This is the main bridge: all UC emulation results proved in `RustM`
    transfer automatically to `SPComp` via this morphism. -/
noncomputable def rustToSPComp : UCMonadMorphism RustM SPComp where
  lift := liftRust
  lift_pure := fun a => by simp [liftRust, pure, Pure.pure]
  lift_bind := fun m f => liftRust_bind m f
  lift_ucMapSum := fun f g x => liftRust_mapSum f g x
  lift_nonexpansive := fun f g => liftRust_nonexpansive f g

/-! ## Section 4: PanicFree Predicate -/

/-- A `RustM` function is panic-free if it always returns `.ok`. -/
def PanicFree {α β : Type} (f : α → RustM β) : Prop :=
  ∀ a, ∃ v, f a = .ok v

/-- A `RustM` computation is panic-free (nullary version). -/
def PanicFree₀ {α : Type} (x : RustM α) : Prop :=
  ∃ v, x = .ok v

/-- Extract the pure function from a panic-free `RustM` function. -/
noncomputable def extractPure {α β : Type} (f : α → RustM β) (hf : PanicFree f) :
    α → β :=
  fun a => (hf a).choose

theorem extractPure_spec {α β : Type} (f : α → RustM β) (hf : PanicFree f) (a : α) :
    f a = .ok (extractPure f hf a) :=
  (hf a).choose_spec

/-- When panic-free, `liftRust ∘ f = SPComp.pure ∘ extractPure f`. -/
theorem liftRust_panicFree {α β : Type} (f : α → RustM β) (hf : PanicFree f) :
    (fun a => liftRust (f a)) = (fun a => SPComp.pure (extractPure f hf a)) := by
  funext a
  rw [extractPure_spec f hf a]
  simp [liftRust]

/-- When panic-free, the lifted function is `IsPure`. -/
theorem liftRust_isPure {α : Type} (x : RustM α) (hx : PanicFree₀ x) :
    SPComp.IsPure (liftRust x) := by
  obtain ⟨v, hv⟩ := hx
  rw [hv]; simp [liftRust]
  exact SPComp.pure_isPure v

/-- Bind of panic-free functions is panic-free. -/
theorem PanicFree_bind {α β γ : Type}
    (f : α → RustM β) (g : β → RustM γ)
    (hf : PanicFree f) (hg : PanicFree g) :
    PanicFree (fun a => f a >>= g) := by
  intro a
  obtain ⟨v, hv⟩ := hf a
  obtain ⟨w, hw⟩ := hg v
  exact ⟨w, by simp [hv, hw]⟩

/-- Pure is panic-free. -/
theorem PanicFree_pure {α β : Type} (f : α → β) :
    PanicFree (fun a => (pure (f a) : RustM β)) :=
  fun a => ⟨f a, rfl⟩

/-- A `RustM` function is panic-free on `pre` if it returns `.ok` at every argument
satisfying `pre`. -/
def PanicFreeOn {α β : Type} (pre : α → Prop) (f : α → RustM β) : Prop :=
  ∀ a, pre a → ∃ v, f a = .ok v

/-- `PanicFree` is `PanicFreeOn` at the trivial precondition. -/
theorem panicFree_iff_panicFreeOn {α β : Type} (f : α → RustM β) :
    PanicFree f ↔ PanicFreeOn (fun _ => True) f := by
  simp [PanicFree, PanicFreeOn]

/-- A panic-free function is panic-free on every precondition. -/
theorem PanicFree.panicFreeOn {α β : Type} {f : α → RustM β} (hf : PanicFree f)
    (pre : α → Prop) : PanicFreeOn pre f :=
  fun a _ => hf a

/-- Panic freedom on `pre` holds on every stronger precondition. -/
theorem PanicFreeOn.mono {α β : Type} {pre pre' : α → Prop} {f : α → RustM β}
    (hf : PanicFreeOn pre f) (h : ∀ a, pre' a → pre a) : PanicFreeOn pre' f :=
  fun a ha => hf a (h a ha)

/-- Bind of functions panic-free on `pre` and `mid`, where every value of the first at an
argument satisfying `pre` satisfies `mid`, is panic-free on `pre`. -/
theorem PanicFreeOn_bind {α β γ : Type} {pre : α → Prop} {mid : β → Prop}
    {f : α → RustM β} {g : β → RustM γ} (hf : PanicFreeOn pre f)
    (hpost : ∀ a v, pre a → f a = .ok v → mid v) (hg : PanicFreeOn mid g) :
    PanicFreeOn pre (fun a => f a >>= g) := by
  intro a ha
  obtain ⟨v, hv⟩ := hf a ha
  obtain ⟨w, hw⟩ := hg v (hpost a v ha hv)
  exact ⟨w, by simp [hv, hw]⟩

/-- Pure is panic-free on every precondition. -/
theorem PanicFreeOn_pure {α β : Type} (pre : α → Prop) (f : α → β) :
    PanicFreeOn pre (fun a => (pure (f a) : RustM β)) :=
  fun a _ => ⟨f a, rfl⟩

/-- On an argument satisfying `pre`, a function panic-free on `pre` lifts to
`SPComp.pure` of its value. -/
theorem liftRust_panicFreeOn {α β : Type} {pre : α → Prop} {f : α → RustM β}
    (hf : PanicFreeOn pre f) {a : α} (ha : pre a) :
    ∃ v, f a = .ok v ∧ liftRust (f a) = SPComp.pure v := by
  obtain ⟨v, hv⟩ := hf a ha
  exact ⟨v, hv, by rw [hv]; rfl⟩

/-- On an argument satisfying `pre`, the lift of a function panic-free on `pre` is
`IsPure`. -/
theorem liftRust_isPure_of_panicFreeOn {α β : Type} {pre : α → Prop} {f : α → RustM β}
    (hf : PanicFreeOn pre f) {a : α} (ha : pre a) : SPComp.IsPure (liftRust (f a)) :=
  liftRust_isPure (f a) (hf a ha)

/-! ## Section 5: Convenience for Hax Bridge -/

/-- Lift a Kleisli morphism from `RustM` to `SPComp`. -/
noncomputable def liftKleisli {α β : Type} (f : α → RustM β) : α → SPComp β :=
  fun a => liftRust (f a)

/-- `sdist` of lifted panic-free functions is 0 when the underlying functions agree. -/
theorem sdist_liftRust_eq_zero {α β : Type} (f : α → RustM β) (hf : PanicFree f) :
    sdist (fun a => liftRust (f a)) (fun a => SPComp.pure (extractPure f hf a)) = 0 := by
  rw [liftRust_panicFree f hf]
  simp_all

/-- Key theorem: `liftRust` of `RustM.of_isOk` equals `SPComp.pure`. -/
theorem liftRust_of_isOk {α : Type} (x : RustM α) (h : RustM.isOk x) :
    liftRust x = SPComp.pure (RustM.of_isOk x h) := by
  cases x with
  | ok v => simp [liftRust, RustM.of_isOk]
  | fail e => exact absurd h (by simp [RustM.isOk, Aeneas.Std.ok?])
  | div => exact absurd h (by simp [RustM.isOk, Aeneas.Std.ok?])

end UCMonad.RustMBridge
