/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Bridge.SemPkg
import CatCrypt.Bridge.PkgEval

/-!
# Monoidal Bridge: DeepPackage ↔ PkgInterface SMC

This file connects the concrete package operations (`DeepPackage.par`, `link`)
to the symmetric monoidal category on `PkgInterface` (from `SemPkg.lean`).

## Main Results

* `tensorAppendIso` — `toPkgInterface(I.append J) ≅ toPkgInterface(I) ⊗ toPkgInterface(J)`
* `unitIso` — `toPkgInterface(⟨[]⟩) ≅ 𝟙_`
* `diAppend_assoc` / `diAppend_empty_*` — algebraic laws for `diAppend`
* `appendAssocIso` — coherence iso from `List.append_assoc`
* `tensorAppend_assoc_coherence` — pentagon coherence (stated, see note)

## Architecture

The `PkgInterface` SMC (from `SemPkg.lean`) uses `Sum`-indexed families with
definitional coherence (`funext + cases + rfl`). The concrete `DeepInterface`
uses `List`-indexed families with `diAppend = List.append` as tensor.

The key difficulty: `Fin (m + n)` vs `Fin m ⊕ Fin n`. The `tensorAppendIso`
bridges this gap using `castKl'` (proof-irrelevant transport on Kleisli arrows)
with the roundtrip proofs handled by `castKl'_castKl'_symm` and
`castKl'_dep_fn` (dependent function transport).
-/

namespace CatCrypt.Bridge.MonoidalBridge

open CatCrypt.Core CatCrypt.Deep CatCrypt.Category CatCrypt.Crypto
open CategoryTheory MonoidalCategory

abbrev toPI := DeepInterface.toPkgInterface
abbrev diAppend := DeepInterface.append

/-! ## Family Correspondence -/

variable (I J K : DeepInterface)

private theorem ops_get_left (i : Fin I.ops.length) :
    (I.ops ++ J.ops).get ⟨i.val, by simp; omega⟩ = I.ops.get i := by
  simp [List.get_eq_getElem, List.getElem_append_left]

private theorem ops_get_right (j : Fin J.ops.length) :
    (I.ops ++ J.ops).get ⟨I.ops.length + j.val, by simp⟩ = J.ops.get j := by
  simp [List.get_eq_getElem, List.getElem_append_right]

private theorem ops_get_dispatch_left {k : Fin (I.ops ++ J.ops).length}
    (hk : k.val < I.ops.length) :
    (I.ops ++ J.ops).get k = I.ops.get ⟨k.val, hk⟩ := by
  simp only [List.get_eq_getElem]
  exact List.getElem_append_left hk

private theorem ops_get_dispatch_right {k : Fin (I.ops ++ J.ops).length}
    (hk : ¬(k.val < I.ops.length)) :
    (I.ops ++ J.ops).get k =
      J.ops.get ⟨k.val - I.ops.length, by have := k.isLt; simp at this; omega⟩ := by
  simp only [List.get_eq_getElem]
  exact List.getElem_append_right (by omega)

/-! ## Type-level cast for operation families -/

/-- Transport a Kleisli arrow along an equality of operation triples.
    Defined via `▸` (Eq.mpr) to leverage proof irrelevance. -/
private noncomputable def castKl' {t₁ t₂ : ℕ × Type × Type} (h : t₁ = t₂)
    (f : t₁.2.1 → SPComp t₁.2.2) : t₂.2.1 → SPComp t₂.2.2 :=
  h ▸ f

@[simp] private theorem castKl'_rfl {t : ℕ × Type × Type}
    (f : t.2.1 → SPComp t.2.2) : castKl' rfl f = f := rfl

@[simp] private theorem castKl'_castKl'_symm {t₁ t₂ : ℕ × Type × Type}
    (h₁ : t₁ = t₂) (h₂ : t₂ = t₁) (f : t₁.2.1 → SPComp t₁.2.2) :
    castKl' h₂ (castKl' h₁ f) = f := by subst h₁; rfl

@[simp] private theorem castKl'_trans {t₁ t₂ t₃ : ℕ × Type × Type}
    (h₁ : t₁ = t₂) (h₂ : t₂ = t₃) (f : t₁.2.1 → SPComp t₁.2.2) :
    castKl' h₂ (castKl' h₁ f) = castKl' (h₁.trans h₂) f := by subst h₁; rfl

/-- A dependent function application transports correctly along `castKl'`.
    If `a = b` as indices and `eq` is the induced operation equality,
    then `castKl' eq (f a) = f b`. -/
private theorem castKl'_dep_fn {ι : Type} {F : ι → ℕ × Type × Type}
    {a b : ι} (hab : a = b)
    (f : ∀ i, (F i).2.1 → SPComp (F i).2.2)
    (eq : F a = F b) :
    castKl' eq (f a) = f b := by subst hab; rfl

/-- Two `castKl'` applications to the same target agree when the indices are equal. -/
private theorem castKl'_dep_fn_congr {ι : Type} {F : ι → ℕ × Type × Type}
    {t : ℕ × Type × Type} {a b : ι} (hab : a = b)
    (f : ∀ i, (F i).2.1 → SPComp (F i).2.2)
    (eq_a : F a = t) (eq_b : F b = t) :
    castKl' eq_a (f a) = castKl' eq_b (f b) := by subst hab; rfl

/-! ## Tensor-Append Isomorphism -/

/-- Forward: handler for `diAppend I J` → handler for `toPI I ⊗ toPI J`. -/
noncomputable def appendToTensor :
    toPI (diAppend I J) ⟶ (toPI I ⊗ toPI J) :=
  fun h k => match k with
  | .inl i =>
    castKl' (ops_get_left I J i)
      (h ⟨i.val, by simp [diAppend, DeepInterface.append]; omega⟩)
  | .inr j =>
    castKl' (ops_get_right I J j)
      (h ⟨I.ops.length + j.val, by simp [diAppend, DeepInterface.append]⟩)

/-- Inverse: handler for `toPI I ⊗ toPI J` → handler for `diAppend I J`. -/
noncomputable def tensorToAppend :
    (toPI I ⊗ toPI J) ⟶ toPI (diAppend I J) :=
  fun h k =>
    if hk : k.val < I.ops.length then
      castKl' (ops_get_dispatch_left I J hk).symm (h (.inl ⟨k.val, hk⟩))
    else
      castKl' (ops_get_dispatch_right I J hk).symm
        (h (.inr ⟨k.val - I.ops.length, by
          have := k.isLt; simp [diAppend, DeepInterface.append] at this; omega⟩))

/-- The tensor-append isomorphism in the PkgInterface category.

    This is the fundamental bridge between `DeepInterface.append` (list concat,
    `Fin`-indexed) and `PkgInterface.tensor` (`Sum`-indexed). -/
noncomputable def tensorAppendIso :
    toPI (diAppend I J) ≅ (toPI I ⊗ toPI J) where
  hom := appendToTensor I J
  inv := tensorToAppend I J
  hom_inv_id := by
    funext h k
    simp only [pkg_comp_apply, pkg_id_apply, appendToTensor, tensorToAppend]
    by_cases hk : k.val < I.ops.length
    · simp only [hk, dite_true]
      exact castKl'_castKl'_symm _ _ _
    · simp only [hk, dite_false, castKl'_trans]
      have hval : I.ops.length + (k.val - I.ops.length) = k.val := by omega
      exact castKl'_dep_fn (Fin.ext hval) h _
  inv_hom_id := by
    funext h k
    simp only [pkg_comp_apply, pkg_id_apply, appendToTensor, tensorToAppend]
    cases k with
    | inl i =>
      simp only [i.isLt, dite_true]
      exact castKl'_castKl'_symm _ _ _
    | inr j =>
      simp only [show ¬(I.ops.length + j.val < I.ops.length) by omega, dite_false,
        castKl'_trans]
      have hval : I.ops.length + j.val - I.ops.length = j.val := by omega
      exact castKl'_dep_fn (Fin.ext hval) (fun j => h (.inr j)) _

/-! ## Unit Correspondence -/

/-- The empty deep interface maps to the monoidal unit. -/
noncomputable def unitIso :
    toPI ⟨[]⟩ ≅ (𝟙_ PkgInterface) where
  hom := fun h k => nomatch k
  inv := fun h k => nomatch k
  hom_inv_id := by funext h k; exact nomatch k
  inv_hom_id := by funext h k; exact nomatch k

/-! ## Structural Properties of `diAppend` -/

/-- `diAppend` is associative: `(I ++ J) ++ K = I ++ (J ++ K)` as DeepInterfaces. -/
theorem diAppend_assoc :
    diAppend (diAppend I J) K = diAppend I (diAppend J K) := by
  simp [diAppend, DeepInterface.append, List.append_assoc]

/-- Right unit: `diAppend I ⟨[]⟩ = I`. -/
theorem diAppend_empty_right :
    diAppend I ⟨[]⟩ = I := by
  simp [diAppend, DeepInterface.append]

/-- Left unit: `diAppend ⟨[]⟩ I = I`. -/
theorem diAppend_empty_left :
    diAppend ⟨[]⟩ I = I := rfl

/-- The PkgInterface iso induced by associativity of `diAppend`. -/
noncomputable def appendAssocIso :
    toPI (diAppend (diAppend I J) K) ≅ toPI (diAppend I (diAppend J K)) :=
  eqToIso (congrArg toPI (diAppend_assoc I J K))

/-- The PkgInterface iso from right-unit of `diAppend`. -/
noncomputable def appendEmptyRightIso :
    toPI (diAppend I ⟨[]⟩) ≅ toPI I :=
  eqToIso (congrArg toPI (diAppend_empty_right I))

/-- The PkgInterface iso from left-unit of `diAppend`. -/
noncomputable def appendEmptyLeftIso :
    toPI (diAppend ⟨[]⟩ I) ≅ toPI I :=
  eqToIso (congrArg toPI (diAppend_empty_left I))

/-! ## Coherence

The associator pentagon: the two paths from `toPI((I++J)++K)` to
`toPI I ⊗ (toPI J ⊗ toPI K)` commute.

**Note**: The proof requires unfolding `eqToHom` (from `appendAssocIso`)
into explicit `castKl'` form. The approach is:
1. Define `appendAssocIso` explicitly via `castKl'` (like `tensorAppendIso`)
2. Use `castKl'_trans` + `castKl'_dep_fn` + proof irrelevance
Both paths compute `castKl'` at the same `Fin.val` index with propositionally
equal operation triples, so the casts agree by proof irrelevance.
-/

/-- `eqToHom` on PkgInterface acts as `▸` (transport) on handlers. -/
private theorem eqToHom_handler {I J : DeepInterface} (h_eq : I = J)
    (handler : TypedHandler (toPI I)) :
    eqToHom (congrArg toPI h_eq) handler = h_eq ▸ handler := by
  subst h_eq; rfl

/-- Transport of a handler along a DeepInterface equality is pointwise identity
    up to `castKl'` at the same `Fin.val`. -/
private theorem handler_transport_apply {I J : DeepInterface} (h_eq : I = J)
    (handler : TypedHandler (toPI I)) (k : (toPI J).ι) :
    (h_eq ▸ handler) k =
    castKl' (by subst h_eq; rfl)
      (handler ⟨k.val, by subst h_eq; exact k.isLt⟩) := by
  subst h_eq; rfl

@[simp] private theorem tensorAppendIso_hom :
    (tensorAppendIso I J).hom = appendToTensor I J := rfl

@[simp] private theorem appendAssocIso_hom :
    (appendAssocIso I J K).hom = eqToHom (congrArg toPI (diAppend_assoc I J K)) := rfl

theorem tensorAppend_assoc_coherence :
    (tensorAppendIso (diAppend I J) K).hom ≫
      (tensorAppendIso I J).hom ▷ toPI K ≫
      (α_ (toPI I) (toPI J) (toPI K)).hom =
    (appendAssocIso I J K).hom ≫
      (tensorAppendIso I (diAppend J K)).hom ≫
      toPI I ◁ (tensorAppendIso J K).hom := by
  funext h k
  simp only [pkg_comp_apply, pkgMCS]
  rcases k with i | (j | k')
  · dsimp only
    simp only [tensorAppendIso_hom, appendAssocIso_hom]
    simp only [appendToTensor]
    -- Goal: castKl' ⋯ (castKl' ⋯ (h ⟨↑i, ⋯⟩)) = castKl' ⋯ (eqToHom ⋯ h ⟨↑i, ⋯⟩)
    have he := eqToHom_handler (diAppend_assoc I J K) h
    rw [he, handler_transport_apply]
    simp only [castKl'_trans]
  · dsimp only
    simp only [tensorAppendIso_hom, appendAssocIso_hom]
    simp only [appendToTensor]
    have he := eqToHom_handler (diAppend_assoc I J K) h
    rw [he, handler_transport_apply]
    simp only [castKl'_trans]
  · dsimp only
    simp only [tensorAppendIso_hom, appendAssocIso_hom]
    simp only [appendToTensor]
    have he := eqToHom_handler (diAppend_assoc I J K) h
    rw [he, handler_transport_apply]
    simp only [castKl'_trans]
    -- Goal: castKl' ⋯ (h ⟨(I++J).length + k', ⋯⟩) = castKl' ⋯ (h ⟨I.length + (J.length + k'), ⋯⟩)
    exact castKl'_dep_fn_congr (Fin.ext (by simp [diAppend, DeepInterface.append]; omega)) h _ _

/-! ## Linking = Categorical Composition

`toSemPkg` maps `DeepPackage.link` to composition in `Category DeepInterface`.
This is the fundamental functoriality theorem connecting the concrete package
operation to the categorical structure.

Note: `toSemPkg` is NOT a strict functor — it does not preserve identity exactly.
`toSemPkg(DeepPackage.id I)` returns `fail` on non-interface operations, while
`𝟙 I = SemPkg.id I` passes them through. Identity is only preserved on interface
operations (see `toSemPkg_id_mem` and `evalImpl_link_id_left/right`).
-/

/-- `toSemPkg` preserves linking at the handler level:
    `toSemPkg(link p₁ p₂).resolve = toSemPkg(p₁).resolve ∘ toSemPkg(p₂).resolve`. -/
theorem toSemPkg_link_resolve (p₁ p₂ : DeepPackage) (oracle : Handler) :
    (toSemPkg (DeepPackage.link p₁ p₂)).resolve oracle =
    (toSemPkg p₁).resolve ((toSemPkg p₂).resolve oracle) := by
  funext op dom codom x
  exact toSemPkg_link p₁ p₂ oracle op dom codom x

/-- Transport of a `SemPkg` along an import equality preserves `resolve`. -/
private theorem SemPkg.resolve_transport {I₁ I₂ I_exp : DeepInterface}
    (h : I₁ = I₂) (s : SemPkg I₁ I_exp) :
    (h ▸ s).resolve = s.resolve := by subst h; rfl

/-- `toSemPkg` preserves linking as `SemPkg.comp`:
    `toSemPkg(link p₁ p₂) = toSemPkg(p₁).comp(toSemPkg(p₂))`.

    Requires `p₁.imports = p₂.exports` for the composition to be well-typed. -/
theorem toSemPkg_link_comp (p₁ p₂ : DeepPackage) (h : p₁.imports = p₂.exports) :
    toSemPkg (DeepPackage.link p₁ p₂) = (h ▸ toSemPkg p₁).comp (toSemPkg p₂) := by
  apply SemPkg.ext; funext oracle
  simp only [SemPkg.comp_resolve, SemPkg.resolve_transport]
  exact toSemPkg_link_resolve p₁ p₂ oracle

/-- `eqToHom` in `Category DeepInterface` preserves `resolve`. -/
private theorem eqToHom_resolve {I J : DeepInterface} (h : I = J) :
    (eqToHom h : SemPkg I J).resolve = _root_.id := by subst h; rfl

/-- `toSemPkg` preserves linking as categorical composition `≫` in
    `Category DeepInterface` (where `f ≫ g = g.comp f`):
    `toSemPkg(link p₁ p₂) = toSemPkg(p₂) ≫ eqToHom(h.symm) ≫ toSemPkg(p₁)`. -/
theorem toSemPkg_link_cat (p₁ p₂ : DeepPackage) (h : p₁.imports = p₂.exports) :
    toSemPkg (DeepPackage.link p₁ p₂) =
    toSemPkg p₂ ≫ eqToHom h.symm ≫ toSemPkg p₁ := by
  apply SemPkg.ext; funext oracle
  simp only [CategoryStruct.comp, SemPkg.comp_resolve, eqToHom_resolve, _root_.id]
  exact toSemPkg_link_resolve p₁ p₂ oracle

/-! ## Unitor Coherence

The unitor bridges: the two paths from `toPI(I ++ ⟨[]⟩)` to `toPI(I)` via
(1) the append-empty iso, or (2) tensor-append iso + unitIso + monoidal unitor,
are equal. Similarly for the left unitor.
-/

/-- Right unitor coherence: the two paths from `toPI(I ++ ⟨[]⟩)` to `toPI(I)` agree.
    Path 1: `toPI(I++⟨[]⟩) → toPI(I) ⊗ toPI(⟨[]⟩) → toPI(I) ⊗ 𝟙_ → toPI(I)`
    Path 2: `toPI(I++⟨[]⟩) → toPI(I)` directly via `appendEmptyRightIso`. -/
theorem tensorAppend_rightUnitor_coherence :
    (tensorAppendIso I ⟨[]⟩).hom ≫ (toPI I ◁ unitIso.hom) ≫ (ρ_ (toPI I)).hom =
    (appendEmptyRightIso I).hom := by
  funext h k
  simp only [pkg_comp_apply, pkgMCS, tensorAppendIso_hom, appendToTensor]
  -- RHS: unfold appendEmptyRightIso to eqToHom, then to castKl' form
  simp only [appendEmptyRightIso, eqToIso]
  have he := eqToHom_handler (diAppend_empty_right I) h
  rw [he, handler_transport_apply]

/-- Left unitor coherence: the two paths from `toPI(⟨[]⟩ ++ I)` to `toPI(I)` agree.
    Path 1: `toPI(⟨[]⟩++I) → toPI(⟨[]⟩) ⊗ toPI(I) → 𝟙_ ⊗ toPI(I) → toPI(I)`
    Path 2: `toPI(⟨[]⟩++I) → toPI(I)` directly via `appendEmptyLeftIso`. -/
theorem tensorAppend_leftUnitor_coherence :
    (tensorAppendIso ⟨[]⟩ I).hom ≫ (unitIso.hom ▷ toPI I) ≫ (λ_ (toPI I)).hom =
    (appendEmptyLeftIso I).hom := by
  -- Since diAppend_empty_left I = rfl, appendEmptyLeftIso = eqToIso rfl = Iso.refl
  -- Both sides should be the identity on toPI I
  have : appendEmptyLeftIso I = Iso.refl (toPI I) := by
    simp [appendEmptyLeftIso, diAppend_empty_left]
  rw [this, Iso.refl_hom]
  funext h k
  simp only [pkg_comp_apply, pkg_id_apply, pkgMCS, tensorAppendIso_hom, appendToTensor]
  -- castKl' proof is reflexive when I_left = ⟨[]⟩ (since [] ++ l = l)
  convert castKl'_rfl (h k) using 2
  · simp [diAppend, DeepInterface.append]
  · congr 1; exact Fin.ext (by simp)

/-! ## Braiding Bridge -/

/-- Braiding bridge: composing the tensor-append iso with braiding and the
    inverse tensor-append iso gives the concrete swap. -/
noncomputable def diAppend_braiding_iso :
    toPI (diAppend I J) ≅ toPI (diAppend J I) :=
  tensorAppendIso I J ≪≫ (β_ (toPI I) (toPI J)) ≪≫ (tensorAppendIso J I).symm

end CatCrypt.Bridge.MonoidalBridge
