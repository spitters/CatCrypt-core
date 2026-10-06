/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad
public import CatCryptCore.Category.ProtCategory
public import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# Protocol Bicategory via the coPara Construction

This file constructs the **protocol bicategory**, an instance of the
coPara construction (Capucci–Gavranović, 2022) applied to the cocartesian Kleisli category.

## Structure

* **0-cells**: types
* **1-cells** `a → b`: protocol objects `ProtObj T a b`
* **2-cells**: protocol morphisms `ProtMor` (simulators with commutativity)
* **Horizontal composition**: routes honest output, accumulates interfaces via `⊕`
* **Identity**: `(Empty, pure ∘ inl)`

## Main results

* `Bicategory (ProtBicat T)` — Mathlib bicategory instance
* `sdist_hcomp` — UC composition as bicategorical interchange
-/

@[expose] public section

set_option autoImplicit true -- bicategory: many type-level variables

namespace UCMonad

open CategoryTheory

variable {T : Type → Type} [UCMonadBase T] [LawfulMonad T]

/-! ## Horizontal Composition and Identity -/

/-- Horizontal composition: routes P's honest output through Q. -/
noncomputable def ProtObj.hcomp
    {hon mid out : Type}
    (P : ProtObj T hon mid) (Q : ProtObj T mid out) : ProtObj T hon out where
  iface := P.iface ⊕ Q.iface
  prot := fun a => P.prot a >>= fun x => match x with
    | .inl m => Q.prot m >>= fun y => match y with
      | .inl o => pure (.inl o)
      | .inr j => pure (.inr (.inr j))
    | .inr i => pure (.inr (.inl i))

/-- Identity 1-cell: pass through with empty interface. -/
def ProtObj.hid (α : Type) : ProtObj T α α where
  iface := Empty
  prot := fun a => pure (.inl a)

/-! ## 2-cells: Unitors, Associator, Whiskering

All proofs follow the same pattern: expand `hcomp`/`hid` definitions,
use `bind_assoc`, `pure_bind`, `bind_pure`, `ucMapSum_inl/inr/pure_pure`,
and Sum case analysis. The `comm` fields are Prop, so extensionality
(`ProtMor.ext`) reduces 2-cell equality to simulator equality. -/

noncomputable def leftUnitorHom {a b : Type} (P : ProtObj T a b) :
    ProtMor ((ProtObj.hid (T := T) a).hcomp P) P where
  sim := fun ei => match ei with | .inl e => Empty.elim e | .inr i => pure i
  comm := by
    intro x; show ((ProtObj.hid (T := T) a).hcomp P).prot x >>= _ = P.prot x
    simp only [ProtObj.hcomp, ProtObj.hid]; rw [pure_bind]
    rw [bind_assoc]; refine (bind_congr fun y => ?_).trans (bind_pure _)
    cases y <;> simp [UCMonadBase.ucMapSum_inl, UCMonadBase.ucMapSum_inr]

noncomputable def leftUnitorInv {a b : Type} (P : ProtObj T a b) :
    ProtMor P ((ProtObj.hid (T := T) a).hcomp P) where
  sim := fun i => pure (Sum.inr i)
  comm := by
    intro x; show P.prot x >>= _ = ((ProtObj.hid (T := T) a).hcomp P).prot x
    simp only [ProtObj.hcomp, ProtObj.hid]; rw [pure_bind]
    congr 1; funext y; cases y <;> simp [UCMonadBase.ucMapSum_inl, UCMonadBase.ucMapSum_inr]

noncomputable def rightUnitorHom {a b : Type} (P : ProtObj T a b) :
    ProtMor (P.hcomp (ProtObj.hid (T := T) b)) P where
  sim := fun ie => match ie with | .inl i => pure i | .inr e => Empty.elim e
  comm := by
    intro x; show (P.hcomp (ProtObj.hid (T := T) b)).prot x >>= _ = P.prot x
    simp only [ProtObj.hcomp, ProtObj.hid, bind_assoc, pure_bind]
    refine (bind_congr fun xa => ?_).trans (bind_pure _)
    cases xa <;> simp [UCMonadBase.ucMapSum_inl, UCMonadBase.ucMapSum_inr]

noncomputable def rightUnitorInv {a b : Type} (P : ProtObj T a b) :
    ProtMor P (P.hcomp (ProtObj.hid (T := T) b)) where
  sim := fun i => pure (Sum.inl i)
  comm := by
    intro x; show P.prot x >>= _ = (P.hcomp (ProtObj.hid (T := T) b)).prot x
    simp only [ProtObj.hcomp, ProtObj.hid, pure_bind]
    congr 1; funext xa; cases xa <;> simp [UCMonadBase.ucMapSum_inl, UCMonadBase.ucMapSum_inr]

noncomputable def assocHom {a b c d : Type}
    (P : ProtObj T a b) (Q : ProtObj T b c) (R : ProtObj T c d) :
    ProtMor ((P.hcomp Q).hcomp R) (P.hcomp (Q.hcomp R)) where
  sim := fun x => match x with
    | .inl (.inl i) => pure (Sum.inl i)
    | .inl (.inr j) => pure (Sum.inr (Sum.inl j))
    | .inr k => pure (Sum.inr (Sum.inr k))
  comm := by
    intro x; simp only [ProtObj.hcomp, bind_assoc]
    refine bind_congr fun xa => ?_
    cases xa with
    | inl m =>
      simp only [bind_assoc]
      congr 1; funext yb; cases yb with
      | inl n =>
        simp only [bind_assoc, pure_bind]
        congr 1; funext zc; cases zc with
        | inl o => simp [UCMonadBase.ucMapSum_inl]
        | inr k => simp [UCMonadBase.ucMapSum_inr]
      | inr j => simp [UCMonadBase.ucMapSum_inr]
    | inr i => simp [UCMonadBase.ucMapSum_inr]

noncomputable def assocInv {a b c d : Type}
    (P : ProtObj T a b) (Q : ProtObj T b c) (R : ProtObj T c d) :
    ProtMor (P.hcomp (Q.hcomp R)) ((P.hcomp Q).hcomp R) where
  sim := fun x => match x with
    | .inl i => pure (Sum.inl (Sum.inl i))
    | .inr (.inl j) => pure (Sum.inl (Sum.inr j))
    | .inr (.inr k) => pure (Sum.inr k)
  comm := by
    intro x; simp only [ProtObj.hcomp, bind_assoc]
    refine bind_congr fun xa => ?_
    cases xa with
    | inl m =>
      simp only [bind_assoc]
      congr 1; funext yb; cases yb with
      | inl n =>
        simp only [bind_assoc, pure_bind]
        congr 1; funext zc; cases zc with
        | inl o => simp [UCMonadBase.ucMapSum_inl]
        | inr k => simp [UCMonadBase.ucMapSum_inr]
      | inr j => simp [UCMonadBase.ucMapSum_inr]
    | inr i => simp [UCMonadBase.ucMapSum_inr]

noncomputable def wkLeft {a b c : Type}
    (P : ProtObj T a b) {Q₁ Q₂ : ProtObj T b c} (θ : ProtMor Q₁ Q₂) :
    ProtMor (P.hcomp Q₁) (P.hcomp Q₂) where
  sim := UCMonadBase.ucMapSum (T := T) pure θ.sim
  comm := by
    intro x; simp only [ProtObj.hcomp, bind_assoc]
    refine bind_congr fun xa => ?_
    cases xa with
    | inl m =>
      simp only [bind_assoc]
      -- Factor: (embed y >>= ucMapSum pure (ucMapSum pure θ.sim))
      --       = (ucMapSum pure θ.sim y >>= embed')
      suffices h : (fun y : c ⊕ Q₁.iface =>
          ((match y with
            | Sum.inl o => (pure (Sum.inl o) : T (c ⊕ (P.iface ⊕ Q₁.iface)))
            | Sum.inr j => pure (Sum.inr (Sum.inr j))) >>=
            UCMonadBase.ucMapSum (T := T) pure
              (UCMonadBase.ucMapSum (T := T) pure θ.sim)))
        = (fun y => UCMonadBase.ucMapSum (T := T) pure θ.sim y >>=
            fun z => match z with
            | Sum.inl o => (pure (Sum.inl o) : T (c ⊕ (P.iface ⊕ Q₂.iface)))
            | Sum.inr j => pure (Sum.inr (Sum.inr j))) by
        simp only [h, ← bind_assoc, θ.comm m]
      funext y; cases y with
      | inl o => simp [pure_bind, UCMonadBase.ucMapSum_inl]
      | inr j => simp [pure_bind, UCMonadBase.ucMapSum_inr]
    | inr i =>
      simp only [pure_bind]
      simp [UCMonadBase.ucMapSum_inr, UCMonadBase.ucMapSum_inl]

noncomputable def wkRight {a b c : Type}
    {P₁ P₂ : ProtObj T a b} (η : ProtMor P₁ P₂) (Q : ProtObj T b c) :
    ProtMor (P₁.hcomp Q) (P₂.hcomp Q) where
  sim := UCMonadBase.ucMapSum (T := T) η.sim pure
  comm := by
    intro x; simp only [ProtObj.hcomp]; rw [bind_assoc]
    -- Factor: embed(z) >>= ucMapSum pure (ucMapSum η.sim pure)
    --       = ucMapSum pure η.sim z >>= embed'
    suffices key : ∀ z : b ⊕ P₁.iface,
        ((match z with
          | .inl m => Q.prot m >>= fun y => match y with
            | .inl o => (pure (.inl o) : T (c ⊕ (P₁.iface ⊕ Q.iface)))
            | .inr j => pure (.inr (.inr j))
          | .inr i => pure (.inr (.inl i))) >>=
          UCMonadBase.ucMapSum (T := T) pure (UCMonadBase.ucMapSum (T := T) η.sim pure))
        = (UCMonadBase.ucMapSum (T := T) pure η.sim z >>= fun z' => match z' with
            | .inl m => Q.prot m >>= fun y => match y with
              | .inl o => (pure (.inl o) : T (c ⊕ (P₂.iface ⊕ Q.iface)))
              | .inr j => pure (.inr (.inr j))
            | .inr i' => pure (.inr (.inl i'))) by
      simp_rw [key, ← bind_assoc]
      change (P₁.prot x >>= UCMonadBase.ucMapSum (T := T) pure η.sim) >>= _ = _
      rw [η.comm x]
    intro z; cases z with
    | inl m =>
      simp only [UCMonadBase.ucMapSum_inl, bind_assoc, pure_bind]
      refine bind_congr fun y => ?_; cases y with
      | inl o => simp [UCMonadBase.ucMapSum_inl, pure_bind]
      | inr j => simp [UCMonadBase.ucMapSum_inr, pure_bind]
    | inr i =>
      simp [UCMonadBase.ucMapSum_inr, UCMonadBase.ucMapSum_inl, pure_bind]

/-- Left-summand Kleisli companion to `UCMonadBase.ucMapSum_pure_kleisli`.
    Mirrors `ucMapSum_pure_kleisli` on the LEFT summand: the right summand
    is `pure` on both sides. -/
theorem ucMapSum_kleisli_pure {α β γ δ : Type}
    (f : α → T β) (g : β → T γ) :
    (fun x : α ⊕ δ => UCMonadBase.ucMapSum (T := T) f (pure : δ → T δ) x
        >>= UCMonadBase.ucMapSum g (pure : δ → T δ))
    = UCMonadBase.ucMapSum (fun a => f a >>= g) (pure : δ → T δ) := by
  funext x
  cases x with
  | inl a =>
    simp only [UCMonadBase.ucMapSum_inl, bind_assoc, pure_bind]
  | inr d =>
    simp only [UCMonadBase.ucMapSum_inr, pure_bind]

/-! ## Round-trip proofs -/

theorem leftUnitor_hom_inv {a b : Type} (P : ProtObj T a b) :
    protMor_comp (leftUnitorHom P) (leftUnitorInv P)
    = protMor_id ((ProtObj.hid (T := T) a).hcomp P) := by
  apply ProtMor.ext; funext x
  simp [protMor_comp, leftUnitorHom, leftUnitorInv, protMor_id]
  cases x with | inl e => exact Empty.elim e | inr i => simp

theorem leftUnitor_inv_hom {a b : Type} (P : ProtObj T a b) :
    protMor_comp (leftUnitorInv P) (leftUnitorHom P) = protMor_id P := by
  apply ProtMor.ext; funext x
  simp [protMor_comp, leftUnitorInv, leftUnitorHom, protMor_id]
  exact pure_bind _ _

theorem rightUnitor_hom_inv {a b : Type} (P : ProtObj T a b) :
    protMor_comp (rightUnitorHom P) (rightUnitorInv P)
    = protMor_id (P.hcomp (ProtObj.hid (T := T) b)) := by
  apply ProtMor.ext; funext x
  simp [protMor_comp, rightUnitorHom, rightUnitorInv, protMor_id]
  cases x with | inl i => simp | inr e => exact Empty.elim e

theorem rightUnitor_inv_hom {a b : Type} (P : ProtObj T a b) :
    protMor_comp (rightUnitorInv P) (rightUnitorHom P) = protMor_id P := by
  apply ProtMor.ext; funext x
  simp [protMor_comp, rightUnitorInv, rightUnitorHom, protMor_id]
  exact pure_bind _ _

theorem assoc_hom_inv {a b c d : Type}
    (P : ProtObj T a b) (Q : ProtObj T b c) (R : ProtObj T c d) :
    protMor_comp (assocHom P Q R) (assocInv P Q R)
    = protMor_id ((P.hcomp Q).hcomp R) := by
  apply ProtMor.ext; funext x
  simp [protMor_comp, assocHom, assocInv, protMor_id]
  cases x with
  | inl pq => cases pq <;> simp <;> exact pure_bind _ _
  | inr k => simp; exact pure_bind _ _

theorem assoc_inv_hom {a b c d : Type}
    (P : ProtObj T a b) (Q : ProtObj T b c) (R : ProtObj T c d) :
    protMor_comp (assocInv P Q R) (assocHom P Q R)
    = protMor_id (P.hcomp (Q.hcomp R)) := by
  apply ProtMor.ext; funext x
  simp [protMor_comp, assocInv, assocHom, protMor_id]
  cases x with
  | inl i => simp; exact pure_bind _ _
  | inr qr => cases qr <;> simp <;> exact pure_bind _ _

/-! ## Bicategory Instance -/

/-- Wrapper type for 0-cells of the protocol bicategory. -/
@[reducible] def ProtBicat (_T : Type → Type) := Type

noncomputable instance protBicatStruct :
    CategoryStruct (ProtBicat T) where
  Hom a b := ProtObj T a b
  id a := ProtObj.hid (T := T) a
  comp P Q := ProtObj.hcomp P Q

/-- Bridge instance: Category on `a ⟶ b` in ProtBicat, needed because instance resolution
    doesn't unfold `a ⟶ b` to `ProtObj T a b`. -/
noncomputable instance protBicatHomCategory (a b : ProtBicat T) :
    Category.{0, 1} (a ⟶ b) :=
  inferInstanceAs (Category (ProtObj T a b))

omit [LawfulMonad T] in
/-- Bridge simp lemma: 2-cell composition in ProtBicat unfolds to bind on sim. -/
@[simp] theorem hom_comp_sim {a b : ProtBicat T} {P Q R : a ⟶ b}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).sim = fun x => f.sim x >>= g.sim := rfl

omit [LawfulMonad T] in
/-- Bridge simp lemma: identity 2-cell in ProtBicat unfolds to pure. -/
@[simp] theorem hom_id_sim {a b : ProtBicat T} (P : a ⟶ b) :
    (𝟙 P : P ⟶ P).sim = pure := rfl

noncomputable instance protBicategory :
    Bicategory.{0, 1} (ProtBicat T) where
  homCategory := protBicatHomCategory
  whiskerLeft {_a _b _c} P {_g _h} (θ : ProtMor _ _) :=
    (wkLeft P θ : ProtMor _ _)
  whiskerRight {_a _b _c} {_f _g} (η : ProtMor _ _) Q :=
    (wkRight η Q : ProtMor _ _)
  associator P Q R := {
    hom := assocHom P Q R
    inv := assocInv P Q R
    hom_inv_id := assoc_hom_inv P Q R
    inv_hom_id := assoc_inv_hom P Q R
  }
  leftUnitor P := {
    hom := leftUnitorHom P
    inv := leftUnitorInv P
    hom_inv_id := leftUnitor_hom_inv P
    inv_hom_id := leftUnitor_inv_hom P
  }
  rightUnitor P := {
    hom := rightUnitorHom P
    inv := rightUnitorInv P
    hom_inv_id := rightUnitor_hom_inv P
    inv_hom_id := rightUnitor_inv_hom P
  }
  -- Axiom 1-2: Left whiskering with identity and composition
  whiskerLeft_id P Q := by
    apply ProtMor.ext; simp [wkLeft, UCMonadBase.ucMapSum_pure_pure]; rfl
  whiskerLeft_comp := by
    intro _ _ _ P _ _ _ η θ
    apply ProtMor.ext; simp only [wkLeft, hom_comp_sim]
    exact (UCMonadBase.ucMapSum_pure_kleisli (T := T) η.sim θ.sim).symm
  -- Axiom 3: Whiskering with identity on left
  id_whiskerLeft := by
    intro a b P Q η; apply ProtMor.ext
    simp only [wkLeft, leftUnitorHom, leftUnitorInv, hom_comp_sim]
    funext x; cases x with
    | inl e => exact Empty.elim e
    | inr i => simp [UCMonadBase.ucMapSum_inr, pure_bind]; exact (bind_pure_comp _ _).symm
  -- Axiom 4: Whiskering distributes over horizontal composition on left.
  comp_whiskerLeft := by
    intro a b c d P Q R R' η; apply ProtMor.ext
    simp only [wkLeft, hom_comp_sim, assocHom, assocInv]
    funext x
    -- Forcing the input type to a syntactic Sum so cases works on hcomp's iface
    change (UCMonadBase.ucMapSum (T := T)
              (pure : (P.iface ⊕ Q.iface) → T _) η.sim x : T _) =
           ((match (x : (P.iface ⊕ Q.iface) ⊕ R.iface) with
              | .inl (.inl i) => (pure (Sum.inl i) : T (P.iface ⊕ (Q.iface ⊕ R.iface)))
              | .inl (.inr j) => pure (Sum.inr (Sum.inl j))
              | .inr k => pure (Sum.inr (Sum.inr k))) >>= fun y =>
              UCMonadBase.ucMapSum (T := T) pure
                (UCMonadBase.ucMapSum (T := T) pure η.sim) y >>= fun z =>
                match z with
                | .inl i => (pure (Sum.inl (Sum.inl i)) : T ((P.iface ⊕ Q.iface) ⊕ R'.iface))
                | .inr (.inl j) => pure (Sum.inl (Sum.inr j))
                | .inr (.inr k) => pure (Sum.inr k))
    cases x with
    | inl pq =>
      cases pq with
      | inl i =>
        simp only [UCMonadBase.ucMapSum_inl, pure_bind]
        -- Reuse ucMapSum_pure_left to discharge LHS
        exact ucMapSum_pure_left _ (Sum.inl i)
      | inr j =>
        simp only [UCMonadBase.ucMapSum_inl, UCMonadBase.ucMapSum_inr, pure_bind]
        exact ucMapSum_pure_left _ (Sum.inr j)
    | inr k =>
      simp only [UCMonadBase.ucMapSum_inr, pure_bind, bind_assoc]
      exact UCMonadBase.ucMapSum_inr (T := T) (pure : (P.iface ⊕ Q.iface) → T _) η.sim k
  -- Axiom 5-6: Right whiskering with identity and composition
  id_whiskerRight P Q := by
    apply ProtMor.ext; simp only [wkRight, hom_id_sim, UCMonadBase.ucMapSum_pure_pure]; rfl
  comp_whiskerRight := by
    intro a b c P₁ P₂ P₃ η θ Q; apply ProtMor.ext
    simp only [wkRight, hom_comp_sim]
    exact (ucMapSum_kleisli_pure (T := T) η.sim θ.sim).symm
  -- Axiom 7-8: Right whiskering with identity and composition on right
  whiskerRight_id := by
    intro a b P Q η; apply ProtMor.ext
    simp only [wkRight, rightUnitorHom, rightUnitorInv, hom_comp_sim]
    funext x
    cases x with
    | inl i =>
      simp [UCMonadBase.ucMapSum_inl, pure_bind]; exact (bind_pure_comp _ _).symm
    | inr e => exact Empty.elim e
  whiskerRight_comp := by
    intro a b c d P P' η Q R; apply ProtMor.ext
    simp only [wkRight, hom_comp_sim, assocHom, assocInv]
    funext x
    -- Force input type so we can cases on the Sum
    change (UCMonadBase.ucMapSum (T := T) η.sim
              (pure : (Q.iface ⊕ R.iface) → T _) x : T _) =
           ((match (x : P.iface ⊕ (Q.iface ⊕ R.iface)) with
              | .inl i => (pure (Sum.inl (Sum.inl i))
                    : T ((P.iface ⊕ Q.iface) ⊕ R.iface))
              | .inr (.inl j) => pure (Sum.inl (Sum.inr j))
              | .inr (.inr k) => pure (Sum.inr k)) >>= fun y =>
              UCMonadBase.ucMapSum (T := T)
                (UCMonadBase.ucMapSum (T := T) η.sim pure) pure y >>= fun z =>
                match z with
                | .inl (.inl i) => (pure (Sum.inl i)
                    : T (P'.iface ⊕ (Q.iface ⊕ R.iface)))
                | .inl (.inr j) => pure (Sum.inr (Sum.inl j))
                | .inr k => pure (Sum.inr (Sum.inr k)))
    cases x with
    | inl i =>
      simp only [UCMonadBase.ucMapSum_inl, pure_bind, bind_assoc]
      exact UCMonadBase.ucMapSum_inl (T := T) η.sim
        (pure : (Q.iface ⊕ R.iface) → T _) i
    | inr qr =>
      cases qr with
      | inl j =>
        simp only [UCMonadBase.ucMapSum_inr, UCMonadBase.ucMapSum_inl, pure_bind]
        exact ucMapSum_pure_right _ (Sum.inl j)
      | inr k =>
        simp only [UCMonadBase.ucMapSum_inr, pure_bind]
        exact ucMapSum_pure_right _ (Sum.inr k)
  -- Axiom 9: Associativity of whiskering
  whisker_assoc := by
    intro a b c d P Q Q' η R; apply ProtMor.ext
    simp only [wkLeft, wkRight, hom_comp_sim, assocHom, assocInv]
    funext x
    -- Force input type to a syntactic Sum on (P.iface ⊕ Q.iface) ⊕ R.iface
    change (UCMonadBase.ucMapSum (T := T)
              (UCMonadBase.ucMapSum (T := T) pure η.sim)
              (pure : R.iface → T R.iface) x : T _) =
           ((match (x : (P.iface ⊕ Q.iface) ⊕ R.iface) with
              | .inl (.inl i) => (pure (Sum.inl i)
                    : T (P.iface ⊕ (Q.iface ⊕ R.iface)))
              | .inl (.inr j) => pure (Sum.inr (Sum.inl j))
              | .inr k => pure (Sum.inr (Sum.inr k))) >>= fun y =>
              UCMonadBase.ucMapSum (T := T) pure
                (UCMonadBase.ucMapSum (T := T) η.sim pure) y >>= fun z =>
              match z with
              | .inl i => (pure (Sum.inl (Sum.inl i))
                    : T ((P.iface ⊕ Q'.iface) ⊕ R.iface))
              | .inr (.inl j) => pure (Sum.inl (Sum.inr j))
              | .inr (.inr k) => pure (Sum.inr k))
    cases x with
    | inl pq =>
      cases pq with
      | inl i =>
        -- Both sides reduce to pure (Sum.inl (Sum.inl i)) via different chains
        simp only [UCMonadBase.ucMapSum_inl, pure_bind]
        calc UCMonadBase.ucMapSum (T := T)
                (UCMonadBase.ucMapSum (T := T) pure η.sim) pure (Sum.inl (Sum.inl i))
            = UCMonadBase.ucMapSum (T := T) pure η.sim (Sum.inl i) >>=
                fun b => pure (Sum.inl b) :=
              UCMonadBase.ucMapSum_inl _ _ _
          _ = pure (Sum.inl i) >>= fun b => (pure (Sum.inl b) : T _) := by
              rw [UCMonadBase.ucMapSum_inl, pure_bind]
          _ = pure (Sum.inl (Sum.inl i)) := pure_bind _ _
      | inr j =>
        simp only [UCMonadBase.ucMapSum_inr, UCMonadBase.ucMapSum_inl, pure_bind, bind_assoc]
        calc UCMonadBase.ucMapSum (T := T)
                (UCMonadBase.ucMapSum (T := T) pure η.sim) pure (Sum.inl (Sum.inr j))
            = UCMonadBase.ucMapSum (T := T) pure η.sim (Sum.inr j) >>=
                fun b => pure (Sum.inl b) :=
              UCMonadBase.ucMapSum_inl _ _ _
          _ = (η.sim j >>= fun b => pure (Sum.inr b)) >>=
                fun b => (pure (Sum.inl b) : T _) := by
              rw [UCMonadBase.ucMapSum_inr]
          _ = η.sim j >>= fun b' => pure (Sum.inl (Sum.inr b')) := by
              rw [bind_assoc]; exact bind_congr fun b' => by rw [pure_bind]
    | inr k =>
      simp only [UCMonadBase.ucMapSum_inr, pure_bind]
      calc UCMonadBase.ucMapSum (T := T)
              (UCMonadBase.ucMapSum (T := T) pure η.sim) pure (Sum.inr k)
          = pure k >>= fun d => pure (Sum.inr d) :=
            UCMonadBase.ucMapSum_inr _ _ _
        _ = pure (Sum.inr k) := pure_bind _ _
  -- Axiom 10: Exchange law (key bicategory axiom)
  whisker_exchange := by
    intro a b c P₁ P₂ Q₁ Q₂ η θ; apply ProtMor.ext
    simp only [wkLeft, wkRight, hom_comp_sim]
    funext x
    cases x with
    | inl m =>
      -- LHS: ucMapSum pure θ.sim (inl m) >>= ucMapSum η.sim pure
      --    = (pure m >>= fun b => pure (inl b)) >>= ucMapSum η.sim pure
      --    = pure (inl m) >>= ucMapSum η.sim pure
      --    = η.sim m >>= fun b => pure (inl b)
      -- RHS: ucMapSum η.sim pure (inl m) >>= ucMapSum pure θ.sim
      --    = (η.sim m >>= fun b => pure (inl b)) >>= ucMapSum pure θ.sim
      --    = η.sim m >>= fun b => (pure (inl b) >>= ucMapSum pure θ.sim)
      --    = η.sim m >>= fun b => (pure b >>= fun x => pure (inl x))
      --    = η.sim m >>= fun b => pure (inl b)
      simp only [UCMonadBase.ucMapSum_inl, pure_bind]
      -- Force the inner type to be the unfolded Sum (so bind_assoc can fire)
      change (pure (Sum.inl m : P₁.iface ⊕ Q₂.iface) : T _) >>=
              UCMonadBase.ucMapSum (T := T) η.sim pure
            = (η.sim m >>= fun b => (pure (Sum.inl b) : T (P₂.iface ⊕ Q₁.iface)))
                >>= UCMonadBase.ucMapSum (T := T) pure θ.sim
      rw [bind_assoc, pure_bind, UCMonadBase.ucMapSum_inl]
      refine bind_congr fun b' => ?_
      rw [pure_bind, UCMonadBase.ucMapSum_inl, pure_bind]
    | inr i =>
      -- Symmetric: both sides reduce to θ.sim i >>= fun d => pure (inr d)
      simp only [UCMonadBase.ucMapSum_inr, pure_bind]
      change (θ.sim i >>= fun d => (pure (Sum.inr d) : T (P₁.iface ⊕ Q₂.iface)))
              >>= UCMonadBase.ucMapSum (T := T) η.sim pure
            = (pure (Sum.inr i : P₂.iface ⊕ Q₁.iface) : T _)
                >>= UCMonadBase.ucMapSum (T := T) pure θ.sim
      rw [bind_assoc, pure_bind, UCMonadBase.ucMapSum_inr]
      refine bind_congr fun d' => ?_
      rw [pure_bind, UCMonadBase.ucMapSum_inr, pure_bind]
  -- Axiom 11: Pentagon identity (4-fold associativity coherence).
  -- Each branch of the 4-deep `Sum` case split is a chain of `pure_bind` and
  -- `ucMapSum_inl`/`ucMapSum_inr` steps; the `assocHom` matchers are typed at
  -- `hcomp`-projected interfaces, so the rewrites unify at default transparency (`erw`).
  pentagon := by
    intro a b c d e P Q R S; apply ProtMor.ext
    simp only [wkLeft, wkRight, hom_comp_sim, assocHom]
    funext x
    rcases x with ⟨⟨val | val⟩ | val⟩ | val
    all_goals
      repeat (first
        | erw [pure_bind]
        | erw [UCMonadBase.ucMapSum_inl]
        | erw [UCMonadBase.ucMapSum_inr])
      rfl
  -- Axiom 12: Triangle identity
  triangle := by
    intro a b c P Q; apply ProtMor.ext
    simp only [wkLeft, wkRight, hom_comp_sim, assocHom, leftUnitorHom, rightUnitorHom]
    funext x
    cases x with
    | inl pe =>
      cases pe with
      | inl i =>
        repeat (first
          | erw [pure_bind]
          | erw [UCMonadBase.ucMapSum_inl]
          | erw [UCMonadBase.ucMapSum_inr])
      | inr e => exact Empty.elim e
    | inr k =>
      repeat (first
        | erw [pure_bind]
        | erw [UCMonadBase.ucMapSum_inl]
        | erw [UCMonadBase.ucMapSum_inr])

end UCMonad

/-! ## UC Interchange Law -/

namespace UCMonad

open scoped ENNReal

/-- **UC interchange**: horizontal composition preserves sdist additively.

    This is the enriched interchange law of the protocol bicategory.

    The proof factors `hcomp` as a Kleisli composition `p ⊛ K_q`, then applies
    `ucSdist_comp_add`. The coproduct PPL step (bounding `ucSdist K_{π₂} K_{F₂}`)
    requires that `ucMapSum` is non-expansive on each component, which holds
    for all concrete instances (SPComp, SDistr, QComp, RoundM, IPDLM).

    The hypothesis `hK` abstracts this step, so that the proof works over
    any `UCMonadMetric` instance satisfying it. -/
theorem sdist_hcomp {T : Type → Type} [UCMonadMetric T]
    {a b c I₁ I₂ : Type} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ F₁ : a → T (b ⊕ I₁)} {π₂ F₂ : b → T (c ⊕ I₂)}
    (h₁ : UCMonadMetric.ucSdist π₁ F₁ ≤ ε₁)
    (h₂ : UCMonadMetric.ucSdist π₂ F₂ ≤ ε₂)
    (hcoPPL : ∀ (f₁ f₂ : b → T (c ⊕ I₂)) (g : I₁ → T I₁),
      UCMonadMetric.ucSdist (UCMonadBase.ucMapSum f₁ g)
        (UCMonadBase.ucMapSum f₂ g) ≤ UCMonadMetric.ucSdist f₁ f₂) :
    let mk (p : a → T (b ⊕ I₁)) (q : b → T (c ⊕ I₂)) : a → T (c ⊕ (I₁ ⊕ I₂)) :=
      fun a => p a >>= fun x => match x with
        | Sum.inl m => q m >>= fun y => match y with
          | Sum.inl o => pure (Sum.inl o) | Sum.inr j => pure (Sum.inr (Sum.inr j))
        | Sum.inr i => pure (Sum.inr (Sum.inl i))
    UCMonadMetric.ucSdist (mk π₁ π₂) (mk F₁ F₂) ≤ ε₁ + ε₂ := by
  intro mk
  -- Factor mk as Kleisli composition: mk p q = fun a => p a >>= K_q
  let K (q : b → T (c ⊕ I₂)) : (b ⊕ I₁) → T (c ⊕ (I₁ ⊕ I₂)) :=
    fun x => match x with
    | Sum.inl m => q m >>= fun y => match y with
      | Sum.inl o => pure (Sum.inl o)
      | Sum.inr j => pure (Sum.inr (Sum.inr j))
    | Sum.inr i => pure (Sum.inr (Sum.inl i))
  have hK : ∀ p q, mk p q = fun a => p a >>= K q := fun _ _ => rfl
  -- K q = ucMapSum q pure ⊛ wrap
  let wrap : (c ⊕ I₂) ⊕ I₁ → T (c ⊕ (I₁ ⊕ I₂)) :=
    fun x => match x with
    | .inl (.inl o) => pure (.inl o)
    | .inl (.inr j) => pure (.inr (.inr j))
    | .inr i => pure (.inr (.inl i))
  have hKq : ∀ q, K q = fun x => UCMonadBase.ucMapSum q pure x >>= wrap := by
    intro q; funext x; cases x with
    | inl m =>
      simp only [K, UCMonadBase.ucMapSum_inl, bind_assoc, pure_bind]
      congr 1; funext y; cases y with
      | inl o => simp [wrap]
      | inr j => simp [wrap]
    | inr i => simp [K, UCMonadBase.ucMapSum_inr, pure_bind, wrap]
  rw [hK, hK, hKq, hKq]
  -- By ucSdist_comp_add, split into π₁/F₁ and K components
  exact ucSdist_comp_add π₁ F₁ _ _ h₁ <| calc
    UCMonadMetric.ucSdist (fun x => UCMonadBase.ucMapSum π₂ pure x >>= wrap)
          (fun x => UCMonadBase.ucMapSum F₂ pure x >>= wrap)
      ≤ UCMonadMetric.ucSdist (UCMonadBase.ucMapSum π₂ pure)
          (UCMonadBase.ucMapSum F₂ pure) :=
        UCMonadMetric.ucSdist_comp_right _ _ wrap
    _ ≤ UCMonadMetric.ucSdist π₂ F₂ := hcoPPL π₂ F₂ pure
    _ ≤ ε₂ := h₂

end UCMonad
