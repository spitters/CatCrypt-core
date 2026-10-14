/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad.RoundM
public import CatCryptCore.Crypto.UCAdmClass.SPCompInstance

/-!
# `UCMonadCompDist` instance for `RoundM`

This file defines the trivial admissibility class and the per-distinguisher decomposition of
`sdistRoundM` on `RoundM n`, so that security levels 2 and 3 (`UCLevels.lean`) apply to
multi-round protocols. It proves that `ucCdist` equals `sdistRoundM` there and that level 2
is equivalent to level 1. The construction follows `UCAdmClass/SPCompInstance.lean`; the
per-distinguisher component is computed on `SPComp` through `flattenAll`:

```
ucDistComp f g D = ⨆ (a : α) (h₀ : Heap),
  absDiff (prTrue (flattenAll(f a) >>= flattenAll∘D) h₀)
          (prTrue (flattenAll(g a) >>= flattenAll∘D) h₀)
```

`liftSPComp` embeds `SPComp` into `RoundM n` with `flattenAll (liftSPComp c) = c`, so the
supremum over `RoundM` distinguishers equals the supremum over `SPComp` distinguishers.

## Main definitions

* `liftSPComp` — embedding of `SPComp` into `RoundM n`
* `roundm_distComp` — the per-distinguisher component

## Main results

* `UCAdmClass (RoundM n)` — trivial admissibility instance
* `UCMonadCompDist (RoundM n)` — per-distinguisher decomposition instance
* `flattenAll_liftSPComp` — `flattenAll (liftSPComp n c) = c`
* `roundm_sdist_eq_iSup` — `sdistRoundM` is the supremum of the per-distinguisher component
* `ucCdist_eq_sdistRoundM` — `ucCdist = sdistRoundM`
* `L2_iff_L1_RoundM` — level 2 is equivalent to level 1 on `RoundM n`

Relation to the literature: `CatCryptCore/Crypto/Complexity.md`.
-/

@[expose] public section

namespace UCMonad.RoundMUC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto UCMonad
open scoped ENNReal

/-! ## Section 1: Trivial Admissibility -/

/-- Trivial admissibility on `RoundM n`: every arrow is admissible. -/
noncomputable instance (n : Nat) : UCAdmClass (RoundM n) where
  adm := fun _ => True
  adm_pure := trivial
  adm_bind := fun _ _ => trivial
  adm_mapSum := fun _ _ => trivial
  adm_precomp := fun _ _ => trivial

/-! ## Section 2: liftSPComp and flattenAll roundtrip -/

/-- Embed an `SPComp` computation into `RoundM n` by immediately finishing. -/
noncomputable def liftSPComp {α : Type} : (n : Nat) → SPComp α → RoundM n α
  | 0, c => c
  | _ + 1, c => SPComp.bind c (fun a => SPComp.pure (.inl a))

/-- `flattenAll ∘ liftSPComp = id`: lifting then flattening is identity. -/
theorem flattenAll_liftSPComp {α : Type} (n : Nat) (c : SPComp α) :
    RoundM.flattenAll n (liftSPComp n c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [liftSPComp, RoundM.flattenAll]
    cases n
    · dsimp only [RoundM.flattenAll, RoundM.flatten]
      simp only [SPComp.bind_assoc, SPComp.pure_bind, SPComp.bind_pure]
    · dsimp only [RoundM.flatten]
      simp only [SPComp.bind_assoc, SPComp.pure_bind]
      exact ih

/-! ## Section 3: Per-Distinguisher Decomposition -/

/-- Per-distinguisher distance component for `RoundM n`, defined via `flattenAll`. -/
noncomputable def roundm_distComp {α β : Type} (n : Nat)
    (f g : α → RoundM n β) (D : β → RoundM n Bool) : ℝ≥0∞ :=
  ⨆ (a : α) (h₀ : Heap),
    absDiff
      (prTrue (SPComp.bind (RoundM.flattenAll n (f a))
        (fun b => RoundM.flattenAll n (D b))) h₀)
      (prTrue (SPComp.bind (RoundM.flattenAll n (g a))
        (fun b => RoundM.flattenAll n (D b))) h₀)

/-- A program is at distance zero from itself for every distinguisher. -/
theorem roundm_distComp_self {α β : Type} (n : Nat)
    (f : α → RoundM n β) (D : β → RoundM n Bool) :
    roundm_distComp n f f D = 0 := by
  simp [roundm_distComp, absDiff_self]

/-- The per-distinguisher distance is symmetric. -/
theorem roundm_distComp_comm {α β : Type} (n : Nat)
    (f g : α → RoundM n β) (D : β → RoundM n Bool) :
    roundm_distComp n f g D = roundm_distComp n g f D := by
  simp only [roundm_distComp]
  congr 1; funext a; congr 1; funext h₀
  exact absDiff_comm _ _

/-- The per-distinguisher distance satisfies the triangle inequality. -/
theorem roundm_distComp_triangle {α β : Type} (n : Nat)
    (f g h : α → RoundM n β) (D : β → RoundM n Bool) :
    roundm_distComp n f h D ≤ roundm_distComp n f g D + roundm_distComp n g h D := by
  apply iSup_le; intro a
  apply iSup_le; intro h₀
  calc absDiff _ _
      ≤ absDiff
          (prTrue (SPComp.bind (RoundM.flattenAll n (f a))
            (fun b => RoundM.flattenAll n (D b))) h₀)
          (prTrue (SPComp.bind (RoundM.flattenAll n (g a))
            (fun b => RoundM.flattenAll n (D b))) h₀) +
        absDiff
          (prTrue (SPComp.bind (RoundM.flattenAll n (g a))
            (fun b => RoundM.flattenAll n (D b))) h₀)
          (prTrue (SPComp.bind (RoundM.flattenAll n (h a))
            (fun b => RoundM.flattenAll n (D b))) h₀) :=
        absDiff_triangle _ _ _
    _ ≤ roundm_distComp n f g D + roundm_distComp n g h D := by
        apply add_le_add
        · exact le_iSup₂_of_le a h₀ le_rfl
        · exact le_iSup₂_of_le a h₀ le_rfl

/-- `sdistRoundM = ⨆ D, roundm_distComp D`.

    The key step: the iSup over `RoundM n` distinguishers equals the
    iSup over `SPComp` distinguishers via `liftSPComp`/`flattenAll` roundtrip. -/
theorem roundm_sdist_eq_iSup {α β : Type} (n : Nat)
    (f g : α → RoundM n β) :
    sdistRoundM n f g = ⨆ D, roundm_distComp n f g D := by
  apply le_antisymm
  · -- sdistRoundM ≤ ⨆ D, roundm_distComp
    -- sdistRoundM n f g = sdist (flattenAll ∘ f) (flattenAll ∘ g)
    --   = ⨆ D_sp a h₀, absDiff(prTrue(bind(flattenAll(f a)) D_sp, h₀), ...)
    -- For each D_sp, take D_rm = liftSPComp ∘ D_sp.
    -- Then flattenAll ∘ D_rm = flattenAll ∘ liftSPComp ∘ D_sp = D_sp.
    unfold sdistRoundM sdist
    apply iSup_le; intro D_sp
    apply iSup_le; intro a
    apply iSup_le; intro h₀
    let D_rm : β → RoundM n Bool := fun b => liftSPComp n (D_sp b)
    have hD : ∀ b, RoundM.flattenAll n (D_rm b) = D_sp b :=
      fun b => flattenAll_liftSPComp n (D_sp b)
    calc absDiff (prTrue (SPComp.bind (RoundM.flattenAll n (f a)) D_sp) h₀)
                 (prTrue (SPComp.bind (RoundM.flattenAll n (g a)) D_sp) h₀)
        = absDiff (prTrue (SPComp.bind (RoundM.flattenAll n (f a))
            (fun b => RoundM.flattenAll n (D_rm b))) h₀)
          (prTrue (SPComp.bind (RoundM.flattenAll n (g a))
            (fun b => RoundM.flattenAll n (D_rm b))) h₀) := by
          simp only [hD]
      _ ≤ roundm_distComp n f g D_rm := le_iSup₂_of_le a h₀ le_rfl
      _ ≤ ⨆ D, roundm_distComp n f g D := le_iSup _ D_rm
  · -- ⨆ D, roundm_distComp ≤ sdistRoundM
    -- For each RoundM D, flattenAll ∘ D is an SPComp distinguisher.
    apply iSup_le; intro D
    apply iSup_le; intro a
    apply iSup_le; intro h₀
    unfold sdistRoundM sdist
    exact le_iSup₂_of_le (fun b => RoundM.flattenAll n (D b)) a
      (le_iSup_of_le h₀ le_rfl)

/-- `bind_right`: post-composition absorbs into the distinguisher via `flattenAll_bind`. -/
theorem roundm_distComp_bind_right {α β γ : Type} (n : Nat)
    (f g : α → RoundM n β) (k : β → RoundM n γ) (D : γ → RoundM n Bool) :
    roundm_distComp n (fun a => f a >>= k) (fun a => g a >>= k) D =
    roundm_distComp n f g (fun b => k b >>= D) := by
  simp only [roundm_distComp]
  congr 1; funext a; congr 1; funext h₀
  congr 1
  · congr 1
    show SPComp.bind (RoundM.flattenAll n (RoundM.bind' n (f a) k))
      (fun c => RoundM.flattenAll n (D c))
      = SPComp.bind (RoundM.flattenAll n (f a))
        (fun b => RoundM.flattenAll n (RoundM.bind' n (k b) D))
    rw [flattenAll_bind]; rw [SPComp.bind_assoc]
    congr 1; funext b; rw [flattenAll_bind]
  · congr 1
    show SPComp.bind (RoundM.flattenAll n (RoundM.bind' n (g a) k))
      (fun c => RoundM.flattenAll n (D c))
      = SPComp.bind (RoundM.flattenAll n (g a))
        (fun b => RoundM.flattenAll n (RoundM.bind' n (k b) D))
    rw [flattenAll_bind]; rw [SPComp.bind_assoc]
    congr 1; funext b; rw [flattenAll_bind]

/-- `bind_left`: pre-composition doesn't increase per-distinguisher distance.
    Uses `absDiff_prTrue_bind_le` (convexity) from `SDist.lean`. -/
theorem roundm_distComp_bind_left {α β γ : Type} (n : Nat)
    (f : α → RoundM n β) (g₁ g₂ : β → RoundM n γ) (D : γ → RoundM n Bool) :
    roundm_distComp n (fun a => f a >>= g₁) (fun a => f a >>= g₂) D ≤
    roundm_distComp n g₁ g₂ D := by
  apply iSup_le; intro a
  apply iSup_le; intro h₀
  -- Rewrite using flattenAll_bind
  have eq1 : SPComp.bind (RoundM.flattenAll n (RoundM.bind' n (f a) g₁))
      (fun c => RoundM.flattenAll n (D c))
    = SPComp.bind (RoundM.flattenAll n (f a))
      (fun b => SPComp.bind (RoundM.flattenAll n (g₁ b))
        (fun c => RoundM.flattenAll n (D c))) := by
    rw [flattenAll_bind, SPComp.bind_assoc]
  have eq2 : SPComp.bind (RoundM.flattenAll n (RoundM.bind' n (f a) g₂))
      (fun c => RoundM.flattenAll n (D c))
    = SPComp.bind (RoundM.flattenAll n (f a))
      (fun b => SPComp.bind (RoundM.flattenAll n (g₂ b))
        (fun c => RoundM.flattenAll n (D c))) := by
    rw [flattenAll_bind, SPComp.bind_assoc]
  -- After rewriting, the goal involves the flattened forms
  show absDiff
    (prTrue (SPComp.bind (RoundM.flattenAll n (f a >>= g₁))
      (fun c => RoundM.flattenAll n (D c))) h₀)
    (prTrue (SPComp.bind (RoundM.flattenAll n (f a >>= g₂))
      (fun c => RoundM.flattenAll n (D c))) h₀)
    ≤ roundm_distComp n g₁ g₂ D
  rw [show (f a >>= g₁ : RoundM n γ) = RoundM.bind' n (f a) g₁ from rfl,
      show (f a >>= g₂ : RoundM n γ) = RoundM.bind' n (f a) g₂ from rfl,
      eq1, eq2]
  set ε := roundm_distComp n g₁ g₂ D
  apply absDiff_prTrue_bind_le (RoundM.flattenAll n (f a)) _ _ h₀ ε
  · intro b h'
    exact le_add_of_absDiff_le (le_iSup₂_of_le b h' le_rfl)
  · intro b h'
    exact le_add_of_absDiff_le
      (by rw [absDiff_comm]; exact le_iSup₂_of_le b h' le_rfl)

/-- `flattenAll n (done n a) = SPComp.pure a`: flattening a done value gives pure. -/
theorem flattenAll_done {α : Type} (n : Nat) (a : α) :
    RoundM.flattenAll n (RoundM.done n a) = SPComp.pure a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [RoundM.flattenAll, RoundM.done]
    cases n
    · dsimp only [RoundM.flattenAll, RoundM.flatten]
      exact SPComp.pure_bind _ _
    · dsimp only [RoundM.flatten]
      simp only [SPComp.pure_bind]
      exact ih

/-- Helper: absorb `pure ∘ inl/inr` into the distinguisher via `flattenAll`.
    `flattenAll (f >>= pure ∘ inj) >>= (flattenAll ∘ D) = flattenAll f >>= (flattenAll ∘ D ∘ inj)` -/
theorem roundm_flattenAll_mapSum_step {α β γ : Type} (n : Nat)
    (c : RoundM n α) (inj : α → β) (D : β → RoundM n γ) :
    SPComp.bind (RoundM.flattenAll n (c >>= fun a => pure (inj a)))
      (fun x => RoundM.flattenAll n (D x))
    = SPComp.bind (RoundM.flattenAll n c)
      (fun a => RoundM.flattenAll n (D (inj a))) := by
  rw [show (c >>= fun a => pure (inj a) : RoundM n β) =
    RoundM.bind' n c (fun a => RoundM.done n (inj a)) from rfl]
  rw [flattenAll_bind, SPComp.bind_assoc]
  congr 1; funext a
  rw [flattenAll_done, SPComp.pure_bind]

/-- Per-distinguisher decomposition of `mapSum` for RoundM.
    Case-splits on the sum input; uses `flattenAll` to reduce to SPComp bind-assoc. -/
theorem roundm_distComp_mapSum {α₁ β₁ α₂ β₂ : Type} (n : Nat)
    (f₁ f₂ : α₁ → RoundM n β₁) (g₁ g₂ : α₂ → RoundM n β₂)
    (D : β₁ ⊕ β₂ → RoundM n Bool) :
    roundm_distComp n (mapSumRoundM n f₁ g₁) (mapSumRoundM n f₂ g₂) D ≤
    roundm_distComp n f₁ f₂ (fun b => D (Sum.inl b)) ⊔
    roundm_distComp n g₁ g₂ (fun d => D (Sum.inr d)) := by
  apply iSup_le; intro x
  apply iSup_le; intro h₀
  rcases x with a | c
  · -- .inl a: mapSumRoundM n f₁ g₁ (.inl a) = f₁ a >>= pure ∘ .inl
    simp only [mapSumRoundM_inl, roundm_distComp,
      roundm_flattenAll_mapSum_step n (f₁ a) Sum.inl D,
      roundm_flattenAll_mapSum_step n (f₂ a) Sum.inl D]
    exact le_sup_left.trans' (le_iSup₂_of_le a h₀ le_rfl)
  · -- .inr c: mapSumRoundM n g₁ g₂ (.inr c) = g c >>= pure ∘ .inr
    simp only [mapSumRoundM_inr, roundm_distComp,
      roundm_flattenAll_mapSum_step n (g₁ c) Sum.inr D,
      roundm_flattenAll_mapSum_step n (g₂ c) Sum.inr D]
    exact le_sup_right.trans' (le_iSup₂_of_le c h₀ le_rfl)

/-! ## Section 4: UCMonadCompDist Instance -/

/-- The per-distinguisher decomposition of the statistical distance on `RoundM n`, through
    `flattenAll`. -/
noncomputable instance (n : Nat) : UCMonadCompDist (RoundM n) where
  ucDistComp := roundm_distComp n
  ucSdist_eq_iSup_distComp := roundm_sdist_eq_iSup n
  ucDistComp_bind_right := roundm_distComp_bind_right n
  ucDistComp_bind_left := roundm_distComp_bind_left n
  ucDistComp_self := roundm_distComp_self n
  ucDistComp_comm := roundm_distComp_comm n
  ucDistComp_triangle := roundm_distComp_triangle n
  ucDistComp_mapSum := roundm_distComp_mapSum n

/-! ## Section 5: Bridge Lemmas -/

/-- With trivial admissibility, `ucCdist = sdistRoundM` for `RoundM n`. -/
theorem ucCdist_eq_sdistRoundM {α β : Type} (n : Nat)
    (f g : α → RoundM n β) :
    ucCdist f g = sdistRoundM n f g := by
  apply le_antisymm
  · exact ucCdist_le_ucSdist f g
  · -- sdistRoundM = ucSdist (by instance definition)
    show sdistRoundM n f g ≤ ucCdist f g
    have : sdistRoundM n f g = ⨆ D, UCMonadCompDist.ucDistComp f g D :=
      UCMonadCompDist.ucSdist_eq_iSup_distComp f g
    rw [this]
    apply iSup_le; intro D
    exact le_iSup₂ (f := fun D _ => UCMonadCompDist.ucDistComp f g D) D trivial

/-- With trivial admissibility, Level 2 is equivalent to Level 1 for `RoundM n`. -/
theorem L2_iff_L1_RoundM {hon out leak sim_if view : Type} {ε : ℝ≥0∞} (n : Nat)
    (π : hon → RoundM n (out ⊕ leak))
    (F : hon → RoundM n (out ⊕ sim_if)) :
    UCEmulatesL2 (T := RoundM n) (view := view) ε π F ↔
    UCEmulates (T := RoundM n) (view := view) ε π F := by
  constructor
  · intro h A
    obtain ⟨S, hS⟩ := h A
    exact ⟨S, by rwa [ucCdist_eq_sdistRoundM] at hS⟩
  · exact UCEmulatesL2_of_L1

end UCMonad.RoundMUC
