/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Category.ProtBicat

/-!
# Approximate 2-cells of the protocol bicategory

An approximate 2-cell `P ⟹ Q` at grade `ε` is a simulator
`sim : P.iface → T Q.iface` whose commuting square
`(id ⊕ sim) ∘ₖ P.prot ≈ Q.prot` holds up to `UCMonadMetric.ucSdist ≤ ε`.
The exact 2-cells `ProtMor` are the approximate 2-cells at grade `0` whose
square commutes on the nose.

## Main definitions

* `ProtMorε P Q ε` — a simulator whose square commutes up to `ε`
* `ProtMorε.vcomp` — vertical composition, grade `ε₁ + ε₂`
* `ProtMorε.id` — identity, grade `0`
* `ProtMor.toApprox` — embedding of exact 2-cells at grade `0`
* `ProtMorε.wkLeft`, `ProtMorε.wkRight` — whiskering, grade preserved
* `ProtMorε.hcomp` — horizontal composition, grade `ε₁ + ε₂`

## Main results

* `ucSdist_hcomp_right_le`, `ucSdist_hcomp_left_le` — the distance of two
  horizontal composites with one factor fixed is bounded by the distance of the
  other factors
* `sdist_hcomp_of_approx` — the bound of `sdist_hcomp`, obtained as the
  horizontal composite of two approximate 2-cells with identity simulators

Left whiskering uses the non-expansiveness of `ucMapSum` in its left component,
in the form of the hypothesis `hcoPPL` of `sdist_hcomp`; right whiskering and
vertical composition use only the axioms of `UCMonadMetric`.
-/

@[expose] public section

set_option autoImplicit true -- bicategory: many type-level variables

namespace UCMonad

open scoped ENNReal

variable {T : Type → Type} [UCMonadMetric T]

/-- An approximate 2-cell from `P` to `Q` at grade `ε`: a simulator from `P`'s
interface to `Q`'s interface such that the commuting square of `ProtMor` holds
up to statistical distance `ε`. -/
structure ProtMorε {hon out : Type} (P Q : ProtObj T hon out) (ε : ℝ≥0∞) where
  /-- The simulator: transforms `P`'s interface to `Q`'s interface. -/
  sim : P.iface → T Q.iface
  /-- The square `(id ⊕ sim) ∘ₖ P.prot ≈ Q.prot` commutes up to `ε`. -/
  dist : UCMonadMetric.ucSdist
    (fun a => P.prot a >>= UCMonadBase.ucMapSum pure sim) Q.prot ≤ ε

namespace ProtMorε

/-- Weakening of the grade: a 2-cell at grade `ε` is a 2-cell at any larger grade. -/
def mono {hon out : Type} {P Q : ProtObj T hon out} {ε ε' : ℝ≥0∞}
    (f : ProtMorε P Q ε) (h : ε ≤ ε') : ProtMorε P Q ε' where
  sim := f.sim
  dist := le_trans f.dist h

/-- The identity approximate 2-cell, with the `pure` simulator, at grade `0`. -/
noncomputable def id {hon out : Type} (P : ProtObj T hon out) : ProtMorε P P 0 where
  sim := pure
  dist := by
    have h : (fun a => P.prot a >>= UCMonadBase.ucMapSum (T := T) pure pure) = P.prot := by
      funext a; rw [UCMonadBase.ucMapSum_pure_pure, bind_pure]
    rw [h, UCMonadMetric.ucSdist_self]

/-- Vertical composition: Kleisli-compose the simulators; the grades add. -/
noncomputable def vcomp {hon out : Type} {P Q R : ProtObj T hon out} {ε₁ ε₂ : ℝ≥0∞}
    (f : ProtMorε P Q ε₁) (g : ProtMorε Q R ε₂) : ProtMorε P R (ε₁ + ε₂) where
  sim := fun x => f.sim x >>= g.sim
  dist := by
    have h : (fun a => P.prot a >>= UCMonadBase.ucMapSum pure (fun x => f.sim x >>= g.sim))
        = fun a => (P.prot a >>= UCMonadBase.ucMapSum pure f.sim) >>=
            UCMonadBase.ucMapSum pure g.sim := by
      funext a
      rw [← UCMonadBase.ucMapSum_pure_kleisli f.sim g.sim, ← bind_assoc]
    rw [h]
    exact le_trans
      (UCMonadMetric.ucSdist_triangle _ (fun a => Q.prot a >>= UCMonadBase.ucMapSum pure g.sim) _)
      (add_le_add (le_trans (UCMonadMetric.ucSdist_comp_right _ _ _) f.dist) g.dist)

/-- Unfolding lemma of `vcomp`: the simulator of a vertical composite is the Kleisli
composite of the simulators. -/
@[simp] theorem vcomp_sim {hon out : Type} {P Q R : ProtObj T hon out} {ε₁ ε₂ : ℝ≥0∞}
    (f : ProtMorε P Q ε₁) (g : ProtMorε Q R ε₂) :
    (f.vcomp g).sim = fun x => f.sim x >>= g.sim := rfl

end ProtMorε

/-- The embedding of an exact 2-cell as an approximate 2-cell at grade `0`. -/
noncomputable def ProtMor.toApprox {hon out : Type} {P Q : ProtObj T hon out}
    (f : ProtMor P Q) : ProtMorε P Q 0 where
  sim := f.sim
  dist := by
    have h : (fun a => P.prot a >>= UCMonadBase.ucMapSum pure f.sim) = Q.prot :=
      funext f.comm
    rw [h, UCMonadMetric.ucSdist_self]

/-- Unfolding lemma of `ProtMor.toApprox`: the embedding preserves the simulator. -/
@[simp] theorem ProtMor.toApprox_sim {hon out : Type} {P Q : ProtObj T hon out}
    (f : ProtMor P Q) : f.toApprox.sim = f.sim := rfl

/-! ## Distance of horizontal composites -/

/-- Varying the left factor of a horizontal composite: the distance is bounded by
the distance of the left factors. -/
theorem ucSdist_hcomp_right_le {a b c I : Type} (p₁ p₂ : a → T (b ⊕ I))
    (Q : ProtObj T b c) :
    UCMonadMetric.ucSdist (ProtObj.hcomp (⟨I, p₁⟩ : ProtObj T a b) Q).prot
      (ProtObj.hcomp (⟨I, p₂⟩ : ProtObj T a b) Q).prot ≤ UCMonadMetric.ucSdist p₁ p₂ :=
  by
  let K : b ⊕ I → T (c ⊕ (I ⊕ Q.iface)) :=
    Sum.elim (fun m => Q.prot m >>=
        Sum.elim (fun o => pure (.inl o)) (fun j => pure (.inr (.inr j))))
      (fun i => pure (.inr (.inl i)))
  have hK : ∀ p : a → T (b ⊕ I),
      (ProtObj.hcomp (⟨I, p⟩ : ProtObj T a b) Q).prot = fun x => p x >>= K := by
    intro p; funext x
    simp only [ProtObj.hcomp]
    refine bind_congr fun z => ?_
    cases z with
    | inl m => refine bind_congr fun y => ?_; cases y <;> rfl
    | inr i => rfl
  rw [hK, hK]
  exact UCMonadMetric.ucSdist_comp_right p₁ p₂ K

/-- Varying the right factor of a horizontal composite: the distance is bounded by
the distance of the right factors, under the non-expansiveness of `ucMapSum` in its
left component. -/
theorem ucSdist_hcomp_left_le {a b c I : Type} (P : ProtObj T a b)
    (q₁ q₂ : b → T (c ⊕ I))
    (hcoPPL : ∀ (f₁ f₂ : b → T (c ⊕ I)) (g : P.iface → T P.iface),
      UCMonadMetric.ucSdist (UCMonadBase.ucMapSum f₁ g)
        (UCMonadBase.ucMapSum f₂ g) ≤ UCMonadMetric.ucSdist f₁ f₂) :
    UCMonadMetric.ucSdist (P.hcomp (⟨I, q₁⟩ : ProtObj T b c)).prot
      (P.hcomp (⟨I, q₂⟩ : ProtObj T b c)).prot ≤ UCMonadMetric.ucSdist q₁ q₂ := by
  let wrap : (c ⊕ I) ⊕ P.iface → T (c ⊕ (P.iface ⊕ I)) :=
    Sum.elim (Sum.elim (fun o => pure (.inl o)) (fun j => pure (.inr (.inr j))))
      (fun i => pure (.inr (.inl i)))
  have hK : ∀ q : b → T (c ⊕ I), (P.hcomp (⟨I, q⟩ : ProtObj T b c)).prot =
      fun x => P.prot x >>= fun z => UCMonadBase.ucMapSum q pure z >>= wrap := by
    intro q; funext x
    simp only [ProtObj.hcomp]
    refine bind_congr fun z => ?_
    cases z with
    | inl m =>
      simp only [UCMonadBase.ucMapSum_inl, bind_assoc, pure_bind]
      refine bind_congr fun y => ?_
      cases y <;> rfl
    | inr i => simp only [UCMonadBase.ucMapSum_inr, pure_bind]; rfl
  rw [hK, hK]
  refine le_trans (UCMonadMetric.ucSdist_comp_left _ _ _) ?_
  refine le_trans (UCMonadMetric.ucSdist_comp_right _ _ wrap) ?_
  exact hcoPPL q₁ q₂ pure

/-! ## Whiskering and horizontal composition -/

namespace ProtMorε

/-- Right whiskering of an approximate 2-cell by a 1-cell; the grade is preserved. -/
noncomputable def wkRight {a b c : Type} {P₁ P₂ : ProtObj T a b} {ε : ℝ≥0∞}
    (η : ProtMorε P₁ P₂ ε) (Q : ProtObj T b c) :
    ProtMorε (P₁.hcomp Q) (P₂.hcomp Q) ε where
  sim := UCMonadBase.ucMapSum (T := T) η.sim pure
  dist := by
    let P₁' : ProtObj T a b :=
      ⟨P₂.iface, fun x => P₁.prot x >>= UCMonadBase.ucMapSum pure η.sim⟩
    let η' : ProtMor P₁ P₁' := ⟨η.sim, fun _ => rfl⟩
    have h : (fun x => (P₁.hcomp Q).prot x >>=
        UCMonadBase.ucMapSum pure (UCMonadBase.ucMapSum η.sim pure)) =
        (P₁'.hcomp Q).prot := funext (UCMonad.wkRight η' Q).comm
    refine le_trans (le_of_eq (congrArg (fun f => UCMonadMetric.ucSdist f (P₂.hcomp Q).prot) h)) ?_
    exact le_trans (ucSdist_hcomp_right_le _ P₂.prot Q) η.dist

/-- Left whiskering of an approximate 2-cell by a 1-cell; the grade is preserved,
under the non-expansiveness of `ucMapSum` in its left component. -/
noncomputable def wkLeft {a b c : Type} (P : ProtObj T a b) {Q₁ Q₂ : ProtObj T b c}
    {ε : ℝ≥0∞} (θ : ProtMorε Q₁ Q₂ ε)
    (hcoPPL : ∀ (f₁ f₂ : b → T (c ⊕ Q₂.iface)) (g : P.iface → T P.iface),
      UCMonadMetric.ucSdist (UCMonadBase.ucMapSum f₁ g)
        (UCMonadBase.ucMapSum f₂ g) ≤ UCMonadMetric.ucSdist f₁ f₂) :
    ProtMorε (P.hcomp Q₁) (P.hcomp Q₂) ε where
  sim := UCMonadBase.ucMapSum (T := T) pure θ.sim
  dist := by
    let Q₁' : ProtObj T b c :=
      ⟨Q₂.iface, fun m => Q₁.prot m >>= UCMonadBase.ucMapSum pure θ.sim⟩
    let θ' : ProtMor Q₁ Q₁' := ⟨θ.sim, fun _ => rfl⟩
    have h : (fun x => (P.hcomp Q₁).prot x >>=
        UCMonadBase.ucMapSum pure (UCMonadBase.ucMapSum pure θ.sim)) =
        (P.hcomp Q₁').prot := funext (UCMonad.wkLeft P θ').comm
    refine le_trans (le_of_eq (congrArg (fun f => UCMonadMetric.ucSdist f (P.hcomp Q₂).prot) h)) ?_
    exact le_trans (ucSdist_hcomp_left_le P _ Q₂.prot hcoPPL) θ.dist

/-- Horizontal composition of approximate 2-cells: right whiskering followed by left
whiskering; the grades add. -/
noncomputable def hcomp {a b c : Type} {P₁ P₂ : ProtObj T a b} {Q₁ Q₂ : ProtObj T b c}
    {ε₁ ε₂ : ℝ≥0∞} (η : ProtMorε P₁ P₂ ε₁) (θ : ProtMorε Q₁ Q₂ ε₂)
    (hcoPPL : ∀ (f₁ f₂ : b → T (c ⊕ Q₂.iface)) (g : P₂.iface → T P₂.iface),
      UCMonadMetric.ucSdist (UCMonadBase.ucMapSum f₁ g)
        (UCMonadBase.ucMapSum f₂ g) ≤ UCMonadMetric.ucSdist f₁ f₂) :
    ProtMorε (P₁.hcomp Q₁) (P₂.hcomp Q₂) (ε₁ + ε₂) :=
  (η.wkRight Q₁).vcomp (wkLeft P₂ θ hcoPPL)

end ProtMorε

/-- The bound of `sdist_hcomp` as the horizontal composite of the approximate
2-cells `⟨I₁, π₁⟩ ⟹ ⟨I₁, F₁⟩` and `⟨I₂, π₂⟩ ⟹ ⟨I₂, F₂⟩` whose simulators are the
identity `pure`. -/
theorem sdist_hcomp_of_approx {a b c I₁ I₂ : Type} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ F₁ : a → T (b ⊕ I₁)} {π₂ F₂ : b → T (c ⊕ I₂)}
    (h₁ : UCMonadMetric.ucSdist π₁ F₁ ≤ ε₁)
    (h₂ : UCMonadMetric.ucSdist π₂ F₂ ≤ ε₂)
    (hcoPPL : ∀ (f₁ f₂ : b → T (c ⊕ I₂)) (g : I₁ → T I₁),
      UCMonadMetric.ucSdist (UCMonadBase.ucMapSum f₁ g)
        (UCMonadBase.ucMapSum f₂ g) ≤ UCMonadMetric.ucSdist f₁ f₂) :
    UCMonadMetric.ucSdist (ProtObj.hcomp (⟨I₁, π₁⟩ : ProtObj T a b) ⟨I₂, π₂⟩).prot
      (ProtObj.hcomp (⟨I₁, F₁⟩ : ProtObj T a b) ⟨I₂, F₂⟩).prot ≤ ε₁ + ε₂ := by
  have hid : ∀ {X Y I : Type} (p : X → T (Y ⊕ I)),
      (fun x => p x >>= UCMonadBase.ucMapSum (T := T) pure pure) = p := by
    intro X Y I p; funext x; rw [UCMonadBase.ucMapSum_pure_pure, bind_pure]
  let η : ProtMorε (⟨I₁, π₁⟩ : ProtObj T a b) ⟨I₁, F₁⟩ ε₁ :=
    ⟨pure, by rw [hid]; exact h₁⟩
  let θ : ProtMorε (⟨I₂, π₂⟩ : ProtObj T b c) ⟨I₂, F₂⟩ ε₂ :=
    ⟨pure, by rw [hid]; exact h₂⟩
  refine le_trans (le_of_eq (congrArg (fun f => UCMonadMetric.ucSdist f
    (ProtObj.hcomp (⟨I₁, F₁⟩ : ProtObj T a b) ⟨I₂, F₂⟩).prot) (funext fun x => ?_)))
    (η.hcomp θ hcoPPL).dist
  change _ = _ >>= UCMonadBase.ucMapSum (T := T) (pure : c → T c)
    (fun z : I₁ ⊕ I₂ => UCMonadBase.ucMapSum (T := T) (pure : I₁ → T I₁) pure z >>=
      UCMonadBase.ucMapSum (T := T) pure (pure : I₂ → T I₂))
  simp only [UCMonadBase.ucMapSum_pure_pure, bind_pure]
  exact (bind_pure _).symm

end UCMonad
