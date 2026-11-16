/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad

/-!
# UCMonad Transformer Instances & Monad Morphisms

This file proves that the `ReaderT` monad transformer preserves the `UCMonad` structure,
and defines `UCMonadMorphism` — a non-expansive monad morphism that transfers UC
emulation results between monads.

## Main definitions

* `UCMonadMorphism T T'` — a monad morphism preserving `UCMonadBase` structure
  and non-expansive with respect to `ucSdist`
* `UCMonad (ReaderT R T)` — reader transformer preserves `UCMonad`

## Main results

* `UCEmulates_transfer_sdist` — sdist bounds transfer along a monad morphism
* `UCEmulates_transfer_sameIface` — same-interface UC emulation transfers
* `approxFact_liftM` — approximate factorization transfers along a monad morphism

## Design

The `ReaderT R T` instance generalizes the `IPDLM Γ` instance (which is `ReaderT Γ SDistr`).
The distance takes a supremum over environments: `⨆ r, ucSdist_T (pointwise at r)`.

`ExceptT E T` does NOT preserve the full `UCMonad` structure because:
1. The affine property (`ucBind_fail`) fails: `c >>= (fun _ => fail)` short-circuits
   on the error branch instead of producing `fail`.
2. The left PPL requires a "domain restriction" property (`ucSdist` on a larger input domain
   can be restricted to a subdomain) that doesn't follow from the abstract PPL axioms.
-/

@[expose] public section

open scoped ENNReal

namespace UCMonad

/-! ## Section 1: UCMonadMorphism -/

/-- A non-expansive monad morphism between UCMonad instances.

    Preserves `pure`, `bind`, and `ucMapSum` on the nose, and is non-expansive
    with respect to `ucSdist`. Any such morphism transfers sdist bounds. -/
structure UCMonadMorphism (T T' : Type → Type)
    [UCMonadMetric T] [UCMonadMetric T'] where
  /-- The natural transformation. -/
  lift : {α : Type} → T α → T' α
  /-- Preserves pure. -/
  lift_pure {α : Type} (a : α) : lift (pure a : T α) = (pure a : T' α)
  /-- Preserves bind. -/
  lift_bind {α β : Type} (m : T α) (f : α → T β) :
    lift (m >>= f) = lift m >>= (fun a => lift (f a))
  /-- Preserves ucMapSum. -/
  lift_ucMapSum {α β γ δ : Type} (f : α → T β) (g : γ → T δ) (x : α ⊕ γ) :
    lift (UCMonadBase.ucMapSum f g x) =
    UCMonadBase.ucMapSum (fun a => lift (f a)) (fun c => lift (g c)) x
  /-- Non-expansive: doesn't increase distance. -/
  lift_nonexpansive {α β : Type} (f g : α → T β) :
    UCMonadMetric.ucSdist (fun a => lift (f a)) (fun a => lift (g a))
    ≤ UCMonadMetric.ucSdist f g

/-! ### Transfer theorems -/

/-- Statistical distance bounds transfer along a monad morphism. -/
theorem UCEmulates_transfer_sdist {T T' : Type → Type}
    [UCMonadMetric T] [UCMonadMetric T']
    (η : UCMonadMorphism T T')
    {hon out iface : Type} {ε : ℝ≥0∞}
    {π F : hon → T (out ⊕ iface)}
    (h : UCMonadMetric.ucSdist π F ≤ ε) :
    UCMonadMetric.ucSdist (fun a => η.lift (π a)) (fun a => η.lift (F a)) ≤ ε :=
  le_trans (η.lift_nonexpansive π F) h

/-- Same-interface sdist transfer implies UC emulation transfer. -/
theorem UCEmulates_transfer_of_sdist {T T' : Type → Type}
    [UCMonadMetric T] [UCMonadMetric T']
    (η : UCMonadMorphism T T')
    {hon out iface view : Type} {ε : ℝ≥0∞}
    {π F : hon → T (out ⊕ iface)}
    (h : UCMonadMetric.ucSdist π F ≤ ε) :
    UCEmulates (T := T') (view := view) ε
      (fun a => η.lift (π a)) (fun a => η.lift (F a)) :=
  UCEmulates_of_sdist ε _ _ (UCEmulates_transfer_sdist η h)

/-! ## Section 2: ProtObj/ProtMor Lifting -/

/-- Lift a protocol object via a monad morphism. -/
noncomputable def ProtObj.liftM {T T' : Type → Type}
    [UCMonadMetric T] [UCMonadMetric T']
    {hon out : Type}
    (P : ProtObj T hon out) (η : UCMonadMorphism T T') : ProtObj T' hon out where
  iface := P.iface
  prot := fun a => η.lift (P.prot a)

/-- Lift a protocol morphism via a monad morphism. -/
noncomputable def ProtMor.liftM {T T' : Type → Type}
    [UCMonadMetric T] [UCMonadMetric T']
    {hon out : Type} {P Q : ProtObj T hon out}
    (f : ProtMor P Q) (η : UCMonadMorphism T T') :
    ProtMor (P.liftM η) (Q.liftM η) where
  sim := fun x => η.lift (f.sim x)
  comm := by
    intro a
    -- Goal: η.lift (P.prot a) >>= ucMapSum pure (η.lift ∘ f.sim) = η.lift (Q.prot a)
    -- By f.comm: P.prot a >>= ucMapSum pure f.sim = Q.prot a
    -- Apply η.lift to both sides, then use lift_bind and lift_ucMapSum
    have hcomm := f.comm a
    show η.lift (P.prot a) >>= UCMonadBase.ucMapSum pure (fun x => η.lift (f.sim x))
      = η.lift (Q.prot a)
    rw [← hcomm, η.lift_bind]
    congr 1; funext x
    rw [η.lift_ucMapSum pure f.sim x]
    congr 1
    funext b; exact (η.lift_pure b).symm

/-- Lifting preserves approximate factorization. -/
theorem approxFact_liftM {T T' : Type → Type}
    [UCMonadMetric T] [UCMonadMetric T']
    (η : UCMonadMorphism T T')
    {hon out : Type} {ε : ℝ≥0∞}
    {P Q : ProtObj T hon out}
    (h : approxFact ε P Q) :
    approxFact ε (P.liftM η) (Q.liftM η) := by
  obtain ⟨S, hS⟩ := h
  refine ⟨fun x => η.lift (S x), ?_⟩
  -- Show: ucSdist (η.lift ∘ P.prot) (fun a => η.lift (Q.prot a) >>= ucMapSum pure (η.lift ∘ S)) ≤ ε
  -- Rewrite the target back through η.  `(Q.liftM η).prot a` may already be unfolded
  -- to `η.lift (Q.prot a)` in the goal, so we match against that form directly.
  have target_eq : (fun a => η.lift (Q.prot a) >>= UCMonadBase.ucMapSum pure
      (fun x => η.lift (S x)))
      = (fun a => η.lift (Q.prot a >>= UCMonadBase.ucMapSum pure S)) := by
    funext a; rw [η.lift_bind]; congr 1; funext x
    rw [η.lift_ucMapSum pure S x]; congr 1
    funext b; exact (η.lift_pure b).symm
  show UCMonadMetric.ucSdist (fun a => η.lift (P.prot a))
    (fun a => η.lift (Q.prot a) >>= UCMonadBase.ucMapSum pure
      (fun x => η.lift (S x))) ≤ _
  rw [target_eq]
  -- Now it's: ucSdist (η.lift ∘ P.prot) (η.lift ∘ (fun a => Q.prot a >>= ucMapSum pure S)) ≤ ε
  exact le_trans (η.lift_nonexpansive P.prot
    (fun a => Q.prot a >>= UCMonadBase.ucMapSum pure S)) hS

/-! ## Section 3: ReaderT Preserves UCMonadBase -/

/-- Parallel composition on `Sum` for `ReaderT R T`: apply pointwise. -/
noncomputable def readerT_ucMapSum {R : Type} {T : Type → Type} [UCMonadBase T]
    {α β γ δ : Type} (f : α → ReaderT R T β) (g : γ → ReaderT R T δ) :
    (α ⊕ γ) → ReaderT R T (β ⊕ δ) :=
  fun x r => UCMonadBase.ucMapSum (fun a => f a r) (fun c => g c r) x

theorem readerT_ucMapSum_inl {R : Type} {T : Type → Type} [UCMonadBase T]
    {α β γ δ : Type} (f : α → ReaderT R T β) (g : γ → ReaderT R T δ) (a : α) :
    readerT_ucMapSum f g (.inl a) = (fun r => f a r >>= fun b => pure (.inl b)) := by
  funext r; simp [readerT_ucMapSum, UCMonadBase.ucMapSum_inl]

theorem readerT_ucMapSum_inr {R : Type} {T : Type → Type} [UCMonadBase T]
    {α β γ δ : Type} (f : α → ReaderT R T β) (g : γ → ReaderT R T δ) (c : γ) :
    readerT_ucMapSum f g (.inr c) = (fun r => g c r >>= fun d => pure (.inr d)) := by
  funext r; simp [readerT_ucMapSum, UCMonadBase.ucMapSum_inr]

theorem readerT_ucMapSum_pure_pure {R : Type} {T : Type → Type} [UCMonadBase T]
    {α β : Type} :
    readerT_ucMapSum (pure : α → ReaderT R T α) (pure : β → ReaderT R T β) = pure := by
  funext x r
  show UCMonadBase.ucMapSum (fun a => (pure a : T α)) (fun b => (pure b : T β)) x = pure x
  exact congr_fun UCMonadBase.ucMapSum_pure_pure x

theorem readerT_ucMapSum_pure_kleisli {R : Type} {T : Type → Type} [UCMonadBase T]
    {α β γ δ : Type} (f : β → ReaderT R T γ) (g : γ → ReaderT R T δ) :
    (fun x : α ⊕ β => readerT_ucMapSum pure f x >>= readerT_ucMapSum pure g)
    = readerT_ucMapSum pure (fun b => f b >>= g) := by
  funext x r
  show UCMonadBase.ucMapSum (fun a => (pure a : T α)) (fun b => f b r) x >>=
      (fun y => UCMonadBase.ucMapSum (fun a => (pure a : T α)) (fun c => g c r) y) =
    UCMonadBase.ucMapSum (fun a => (pure a : T α)) (fun b => f b r >>= fun c => g c r) x
  exact congr_fun (UCMonadBase.ucMapSum_pure_kleisli (fun b => f b r) (fun c => g c r)) x

/-! ## Section 4: ReaderT Statistical Distance -/

/-- Statistical distance for `ReaderT R T`: worst-case over environments.

    `sdistR f g = ⨆ r, ucSdist_T (fun a => f a r) (fun a => g a r)`

    This generalizes `sdistI` from `IPDLInstance.lean` (where `T = SDistr`). -/
noncomputable def sdistR {R : Type} {T : Type → Type} [UCMonadMetric T]
    {α β : Type} (f g : α → ReaderT R T β) : ℝ≥0∞ :=
  ⨆ (r : R), UCMonadMetric.ucSdist (fun a => f a r) (fun a => g a r)

theorem sdistR_self {R : Type} {T : Type → Type} [UCMonadMetric T]
    {α β : Type} (f : α → ReaderT R T β) : sdistR f f = 0 := by
  simp [sdistR, UCMonadMetric.ucSdist_self]

theorem sdistR_sym {R : Type} {T : Type → Type} [UCMonadMetric T]
    {α β : Type} (f g : α → ReaderT R T β) : sdistR f g = sdistR g f := by
  simp only [sdistR, UCMonadMetric.ucSdist_sym]

theorem sdistR_triangle {R : Type} {T : Type → Type} [UCMonadMetric T]
    {α β : Type} (f g h : α → ReaderT R T β) :
    sdistR f h ≤ sdistR f g + sdistR g h := by
  apply iSup_le; intro r
  calc UCMonadMetric.ucSdist (fun a => f a r) (fun a => h a r)
      ≤ UCMonadMetric.ucSdist (fun a => f a r) (fun a => g a r)
        + UCMonadMetric.ucSdist (fun a => g a r) (fun a => h a r) :=
        UCMonadMetric.ucSdist_triangle _ _ _
    _ ≤ sdistR f g + sdistR g h := add_le_add
        (le_iSup_of_le r le_rfl) (le_iSup_of_le r le_rfl)

/-- Right PPL for ReaderT: post-composition doesn't increase distance. -/
theorem sdistR_comp_right {R : Type} {T : Type → Type} [UCMonadMetric T]
    {α β γ : Type} (f g : α → ReaderT R T β) (k : β → ReaderT R T γ) :
    sdistR (fun a => f a >>= k) (fun a => g a >>= k) ≤ sdistR f g := by
  apply iSup_le; intro r
  show UCMonadMetric.ucSdist (fun a => f a r >>= fun b => k b r)
      (fun a => g a r >>= fun b => k b r) ≤ _
  calc UCMonadMetric.ucSdist (fun a => f a r >>= fun b => k b r)
          (fun a => g a r >>= fun b => k b r)
      ≤ UCMonadMetric.ucSdist (fun a => f a r) (fun a => g a r) :=
        UCMonadMetric.ucSdist_comp_right _ _ _
    _ ≤ sdistR f g := le_iSup_of_le r le_rfl

/-- Left PPL for ReaderT: pre-composition with shared prefix doesn't increase distance. -/
theorem sdistR_comp_left {R : Type} {T : Type → Type} [UCMonadMetric T]
    {α β γ : Type} (f : α → ReaderT R T β) (g₁ g₂ : β → ReaderT R T γ) :
    sdistR (fun a => f a >>= g₁) (fun a => f a >>= g₂) ≤ sdistR g₁ g₂ := by
  apply iSup_le; intro r
  show UCMonadMetric.ucSdist (fun a => f a r >>= fun b => g₁ b r)
      (fun a => f a r >>= fun b => g₂ b r) ≤ _
  calc UCMonadMetric.ucSdist (fun a => f a r >>= fun b => g₁ b r)
          (fun a => f a r >>= fun b => g₂ b r)
      ≤ UCMonadMetric.ucSdist (fun b => g₁ b r) (fun b => g₂ b r) :=
        UCMonadMetric.ucSdist_comp_left _ _ _
    _ ≤ sdistR g₁ g₂ := le_iSup_of_le r le_rfl

/-! ## Section 5: ReaderT UCMonad Instance -/

/-- Affine property for ReaderT: binding with fail gives fail. -/
theorem readerT_bind_fail {R : Type} {T : Type → Type} [UCMonadAffine T]
    {α β : Type} (c : ReaderT R T α) :
    (c >>= fun _ => (fun (_ : R) => UCMonadAffine.ucFail : ReaderT R T β)) =
    (fun _ => UCMonadAffine.ucFail) := by
  funext r; exact UCMonadAffine.ucBind_fail (c r)

/-- `ReaderT R T` inherits the full `UCMonad` structure from `T`.

    This generalizes the hand-written `IPDLM Γ` instance from `IPDLInstance.lean`
    (where `T = SDistr`). -/
noncomputable instance readerT_UCMonad {R : Type} {T : Type → Type}
    [UCMonad T] : UCMonad (ReaderT R T) where
  ucMapSum := @readerT_ucMapSum R T _
  ucMapSum_inl := fun f g a => readerT_ucMapSum_inl f g a
  ucMapSum_inr := fun f g c => readerT_ucMapSum_inr f g c
  ucMapSum_pure_pure := readerT_ucMapSum_pure_pure
  ucMapSum_pure_kleisli := fun f g => readerT_ucMapSum_pure_kleisli f g
  ucFail := fun _ => UCMonadAffine.ucFail
  ucBind_fail := fun c => readerT_bind_fail c
  ucSdist := @sdistR R T _
  ucSdist_self := sdistR_self
  ucSdist_sym := sdistR_sym
  ucSdist_triangle := sdistR_triangle
  ucSdist_comp_right := sdistR_comp_right
  ucSdist_comp_left := sdistR_comp_left

end UCMonad
