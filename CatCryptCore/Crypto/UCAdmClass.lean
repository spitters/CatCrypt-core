/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad
public import CatCryptCore.Tactics.AutoHopRegistry
public meta import CatCryptCore.Tactics.AutoHopRegistry

/-!
# Admissibility classes and computational distance

This file defines admissibility classes on Kleisli arrows (`UCAdmClass`), the
per-distinguisher decomposition of `ucSdist` (`UCMonadCompDist`), and the computational
distance `ucCdist`, the supremum of the per-distinguisher distance over admissible
distinguishers. It proves that `ucCdist` is a pseudometric bounded by `ucSdist` and that
pre- and post-composition do not increase it. Security levels 2 and 3 (`UCLevels.lean`) are
stated over `ucCdist`.

An admissibility class is closed under `pure`, `bind` and `mapSum`, so the admissible arrows
form a wide subcategory of the Kleisli category of `T`.

## Main definitions

* `UCAdmClass` — admissibility predicate on Kleisli arrows, closed under the monad operations
* `UCMonadCompDist` — per-distinguisher decomposition of `ucSdist`
* `ucCdist` — computational distance, the supremum over admissible distinguishers

## Main results

* `ucCdist_le_ucSdist` — the computational distance is at most the statistical distance
* `ucCdist_self`, `ucCdist_sym`, `ucCdist_triangle` — pseudometric laws
* `ucCdist_comp_right` — post-composition with an admissible arrow does not increase `ucCdist`
* `ucCdist_comp_left` — pre-composition with any arrow does not increase `ucCdist`

Relation to the literature: `CatCryptCore/Crypto/Complexity.md`.

## References

* Patrignani, Künnemann, Wahby, Cecchetti, "Universal Composability Is Robust
  Compilation", TOPLAS 46(4), 2024 — perfect UC (Def. 2)
* Künnemann, Patrignani, Cecchetti, "Computationally Bounded Robust Compilation and
  Universally Composable Security", CSF 2024 — statistical UC (§IV-A), computational UC
  (Def. 3), predicate-parametrised robust compilation (Def. 7)
* Katsumata, "A Double Category Theoretic Analysis of Graded Linear Exponential Comonads",
  FoSSaCS 2018 — categorical semantics of the indexed exponential `!_r`
* Atkey, "Polynomial Time and Dependent Types", POPL 2024 — §2 and Related Work survey the
  linear-typing characterisations of polynomial time
-/

@[expose] public section

open scoped ENNReal

namespace UCMonad

/-! ## Section 1: Admissibility Class -/

/-- An admissibility class on a monad: a predicate on Kleisli arrows closed under the
    monad operations and under precomposition with functions. The admissible arrows form a
    wide subcategory of the Kleisli category Kl(T).

    The closure laws take as their model the closure under composition (cut) of the
    bounded fragments of implicit computational complexity (Bellantoni-Cook, BLL, soft
    affine logic). By `adm_pure` and `adm_precomp` every class contains every pure test
    `pure ∘ p`, whatever the function `p`, so a class bounds the effectful operations of an
    arrow and leaves its pure computation free. The classes on `SPComp` (`spTreeQueryAdm`,
    `spTreeSizeAdm`, the shape class of `CTAdmClass.lean`) bound queries, nodes and shape.
    Computational security is stated per adversary with explicit reductions
    (`CatCryptCore/Crypto/ConcreteSecurity.md`).

    Axioms:
    - `adm_pure`: identity morphisms are admissible
    - `adm_bind`: Kleisli composition preserves admissibility
    - `adm_mapSum`: the coproduct of admissible arrows is admissible
    - `adm_precomp`: precomposition with a function preserves admissibility -/
class UCAdmClass (T : Type → Type) [Monad T] [UCMonadBase T] where
  /-- Predicate marking the admissible Kleisli arrows. -/
  adm : {α β : Type} → (α → T β) → Prop
  /-- `pure` is always admissible. -/
  adm_pure {α : Type} : adm (pure : α → T α)
  /-- Kleisli composition preserves admissibility. -/
  adm_bind {α β γ : Type} {f : α → T β} {g : β → T γ} :
    adm f → adm g → adm (fun a => f a >>= g)
  /-- Coproduct preserves admissibility. -/
  adm_mapSum {α β γ δ : Type} {f : α → T β} {g : γ → T δ} :
    adm f → adm g → adm (UCMonadBase.ucMapSum f g)
  /-- Precomposition with a pure function preserves admissibility.
      Categorically: the wide subcategory of admissible arrows is closed under
      precomposition with deterministic morphisms (Set-maps). -/
  adm_precomp {α α' β : Type} {g : α → T β} (f : α' → α) :
    adm g → adm (g ∘ f)

export UCAdmClass (adm adm_pure adm_bind adm_mapSum adm_precomp)

/-! ## Section 2: Per-Distinguisher Decomposition -/

/-- Decomposition of `ucSdist` into components indexed by distinguishers. The computational
    distance `ucCdist` is the supremum of the components over admissible distinguishers.

    The fields:
    - `ucDistComp_bind_right` = monad associativity at the distribution level
    - `ucDistComp_self/comm/triangle` = pointwise lift of `absDiff` properties
    - `ucSdist_eq_iSup_distComp` = connects to existing abstract metric -/
class UCMonadCompDist (T : Type → Type)
    extends UCMonadMetric T, UCAdmClass T where
  /-- Per-distinguisher distance component. -/
  ucDistComp {α β : Type} (f g : α → T β) (D : β → T Bool) : ℝ≥0∞
  /-- `ucSdist = unrestricted sup of components`. -/
  ucSdist_eq_iSup_distComp {α β : Type} (f g : α → T β) :
    ucSdist f g = ⨆ D, ucDistComp f g D
  /-- Associativity: post-composition absorbs into distinguisher.
      This follows from `bind_assoc` at the distribution level. -/
  ucDistComp_bind_right {α β γ : Type}
    (f g : α → T β) (k : β → T γ) (D : γ → T Bool) :
    ucDistComp (fun a => f a >>= k) (fun a => g a >>= k) D =
    ucDistComp f g (fun b => k b >>= D)
  /-- Reflexivity at per-distinguisher level. -/
  ucDistComp_self {α β : Type} (f : α → T β) (D : β → T Bool) :
    ucDistComp f f D = 0
  /-- Symmetry at per-distinguisher level. -/
  ucDistComp_comm {α β : Type} (f g : α → T β) (D : β → T Bool) :
    ucDistComp f g D = ucDistComp g f D
  /-- Triangle inequality at per-distinguisher level. -/
  ucDistComp_triangle {α β : Type} (f g h : α → T β) (D : β → T Bool) :
    ucDistComp f h D ≤ ucDistComp f g D + ucDistComp g h D
  /-- Pre-composition non-expansiveness at per-distinguisher level: pre-composition doesn't increase distance.
      This follows from sub-probability convexity: the absolute difference of
      weighted averages is bounded by the sup of pointwise differences. -/
  ucDistComp_bind_left {α β γ : Type}
    (f : α → T β) (g₁ g₂ : β → T γ) (D : γ → T Bool) :
    ucDistComp (fun a => f a >>= g₁) (fun a => f a >>= g₂) D ≤
    ucDistComp g₁ g₂ D
  /-- Per-distinguisher decomposition of `mapSum`.
      The distance over sum inputs decomposes as the max of each component.
      This follows from `⨆ (x : α ⊕ β), F x = (⨆ a, F (.inl a)) ⊔ (⨆ b, F (.inr b))`. -/
  ucDistComp_mapSum {α₁ β₁ α₂ β₂ : Type}
    (f₁ f₂ : α₁ → T β₁) (g₁ g₂ : α₂ → T β₂) (D : β₁ ⊕ β₂ → T Bool) :
    ucDistComp (UCMonadBase.ucMapSum f₁ g₁) (UCMonadBase.ucMapSum f₂ g₂) D ≤
    ucDistComp f₁ f₂ (fun b => D (Sum.inl b)) ⊔
    ucDistComp g₁ g₂ (fun d => D (Sum.inr d))

/-! ## Section 3: Computational Distance (Defined, Not Axiomatized) -/

variable {T : Type → Type} [UCMonadCompDist T]

/-- Computational distance: supremum restricted to admissible distinguishers.
    This is a DEFINITION, not an axiom. All metric properties are THEOREMS.

    `ucCdist f g = ⨆ (D : adm D), ucDistComp f g D`

    When `adm = fun _ => True` (trivial admissibility), `ucCdist = ucSdist`. -/
noncomputable def ucCdist {α β : Type}
    (f g : α → T β) : ℝ≥0∞ :=
  ⨆ (D : β → T Bool) (_ : adm D), UCMonadCompDist.ucDistComp f g D

/-! ## Section 4: Derived Metric Properties (All Theorems, 0 Axioms) -/

/-- Computational distance is bounded by statistical distance.
    Proof: restricted supremum ≤ unrestricted supremum. -/
theorem ucCdist_le_ucSdist {α β : Type} (f g : α → T β) :
    ucCdist f g ≤ UCMonadMetric.ucSdist f g := by
  rw [UCMonadCompDist.ucSdist_eq_iSup_distComp]
  apply iSup₂_le
  intro D _
  exact le_iSup _ D

/-- Reflexivity: `ucCdist f f = 0`. -/
theorem ucCdist_self {α β : Type} (f : α → T β) :
    ucCdist f f = 0 := by
  simp only [ucCdist, UCMonadCompDist.ucDistComp_self]
  simp

/-- Symmetry: `ucCdist f g = ucCdist g f`. -/
@[hop_metric] theorem ucCdist_sym {α β : Type} (f g : α → T β) :
    ucCdist f g = ucCdist g f := by
  simp only [ucCdist, UCMonadCompDist.ucDistComp_comm f g]

/-- Triangle inequality: `ucCdist f h ≤ ucCdist f g + ucCdist g h`. -/
@[hop_metric] theorem ucCdist_triangle {α β : Type} (f g h : α → T β) :
    ucCdist f h ≤ ucCdist f g + ucCdist g h := by
  apply iSup₂_le
  intro D hD
  calc UCMonadCompDist.ucDistComp f h D
      ≤ UCMonadCompDist.ucDistComp f g D + UCMonadCompDist.ucDistComp g h D :=
        UCMonadCompDist.ucDistComp_triangle f g h D
    _ ≤ ucCdist f g + ucCdist g h :=
        add_le_add (le_iSup₂ (f := fun D _ => UCMonadCompDist.ucDistComp f g D) D hD)
                   (le_iSup₂ (f := fun D _ => UCMonadCompDist.ucDistComp g h D) D hD)

/-- Post-composition non-expansiveness for computational distance: post-composition with an admissible
    arrow doesn't increase distance.

    **This is a THEOREM, not an axiom.** The proof uses:
    1. `ucDistComp_bind_right`: absorb `k` into the distinguisher
    2. `adm_bind`: `adm k ∧ adm D → adm (k >=> D)`

    **Why `adm k` is necessary**: Let `f = PRG(s)`, `g = random`, `k = range_test`.
    Then `ucCdist f g ≈ 0` but `ucCdist (f >>= k) (g >>= k) ≈ 1`. -/
theorem ucCdist_comp_right {α β γ : Type} (f g : α → T β) (k : β → T γ)
    (hk : adm k) :
    ucCdist (fun a => f a >>= k) (fun a => g a >>= k) ≤ ucCdist f g := by
  apply iSup₂_le
  intro D hD
  rw [UCMonadCompDist.ucDistComp_bind_right]
  exact le_iSup₂ (f := fun D _ => UCMonadCompDist.ucDistComp f g D)
    (fun b => k b >>= D) (adm_bind hk hD)

/-- Pre-composition non-expansiveness for computational distance: pre-composition doesn't increase distance.

    **No `adm` requirement on `f`**: the distinguisher stays the same on both sides,
    so the restriction to admissible D is preserved. Pre-composition only changes
    the input distribution, not the test.

    The proof uses `ucDistComp_bind_left` (sub-probability convexity). -/
theorem ucCdist_comp_left {α β γ : Type} (f : α → T β) (g₁ g₂ : β → T γ) :
    ucCdist (fun a => f a >>= g₁) (fun a => f a >>= g₂) ≤ ucCdist g₁ g₂ := by
  apply iSup₂_le; intro D hD
  exact le_trans (UCMonadCompDist.ucDistComp_bind_left f g₁ g₂ D)
    (le_iSup₂ (f := fun D _ => UCMonadCompDist.ucDistComp g₁ g₂ D) D hD)

/-- Monotonicity: if `ucCdist f g ≤ ε₁ ≤ ε₂`, then `ucCdist f g ≤ ε₂`. -/
theorem ucCdist_mono {α β : Type} {f g : α → T β} {ε₁ ε₂ : ℝ≥0∞}
    (h : ucCdist f g ≤ ε₁) (hle : ε₁ ≤ ε₂) : ucCdist f g ≤ ε₂ :=
  le_trans h hle

/-- Equality implies zero computational distance. -/
theorem ucCdist_le_of_eq {α β : Type} {f g : α → T β} (h : f = g) :
    ucCdist f g = 0 := by
  subst h; exact ucCdist_self f

/-- Composition of ε-close morphisms in ucCdist (additive bound).

    Post-composition non-expansiveness still requires `adm g₁` (post-composition changes the distinguisher).
    Pre-composition non-expansiveness is now sharp: bounds by `ucCdist g₁ g₂` (not `ucSdist`). -/
theorem ucCdist_comp_add {α β γ : Type}
    (f₁ f₂ : α → T β) (g₁ g₂ : β → T γ) {ε₁ ε₂ : ℝ≥0∞}
    (hf : ucCdist f₁ f₂ ≤ ε₁) (hk : adm g₁)
    (hg : ucCdist g₁ g₂ ≤ ε₂) :
    ucCdist (fun a => f₁ a >>= g₁) (fun a => f₂ a >>= g₂) ≤ ε₁ + ε₂ := by
  calc ucCdist (fun a => f₁ a >>= g₁) (fun a => f₂ a >>= g₂)
      ≤ ucCdist (fun a => f₁ a >>= g₁) (fun a => f₂ a >>= g₁)
        + ucCdist (fun a => f₂ a >>= g₁) (fun a => f₂ a >>= g₂) :=
        ucCdist_triangle _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add
        (le_trans (ucCdist_comp_right f₁ f₂ g₁ hk) hf)
        (le_trans (ucCdist_comp_left f₂ g₁ g₂) hg)

/-! ## Section 5: Parallel Composition (mapSum) -/

/-- Parallel composition bound for `ucCdist`:
    `ucCdist (mapSum f₁ g₁) (mapSum f₂ g₂) ≤ max(ucCdist f₁ f₂, ucCdist g₁ g₂)`.

    Uses `ucDistComp_mapSum` to decompose per-distinguisher, then `adm_precomp`
    to ensure each component is in the admissible range. -/
theorem ucCdist_mapSum_le {α₁ β₁ α₂ β₂ : Type}
    (f₁ f₂ : α₁ → T β₁) (g₁ g₂ : α₂ → T β₂)
    {ε₁ ε₂ : ℝ≥0∞}
    (hf : ucCdist f₁ f₂ ≤ ε₁) (hg : ucCdist g₁ g₂ ≤ ε₂) :
    ucCdist (UCMonadBase.ucMapSum f₁ g₁) (UCMonadBase.ucMapSum f₂ g₂) ≤ ε₁ ⊔ ε₂ := by
  apply iSup₂_le; intro D hD
  calc UCMonadCompDist.ucDistComp (UCMonadBase.ucMapSum f₁ g₁)
        (UCMonadBase.ucMapSum f₂ g₂) D
      ≤ UCMonadCompDist.ucDistComp f₁ f₂ (fun b => D (Sum.inl b)) ⊔
        UCMonadCompDist.ucDistComp g₁ g₂ (fun d => D (Sum.inr d)) :=
        UCMonadCompDist.ucDistComp_mapSum f₁ f₂ g₁ g₂ D
    _ ≤ ucCdist f₁ f₂ ⊔ ucCdist g₁ g₂ := by
        apply sup_le_sup
        · exact le_iSup₂ (f := fun D _ => UCMonadCompDist.ucDistComp f₁ f₂ D)
            (fun b => D (Sum.inl b)) (adm_precomp Sum.inl hD)
        · exact le_iSup₂ (f := fun D _ => UCMonadCompDist.ucDistComp g₁ g₂ D)
            (fun d => D (Sum.inr d)) (adm_precomp Sum.inr hD)
    _ ≤ ε₁ ⊔ ε₂ := sup_le_sup hf hg

end UCMonad
