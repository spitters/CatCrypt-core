/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Bridge.SemPkg
import CatCryptCore.Bridge.PkgEval

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

/-- Sum-indexed variant of `castKl'_dep_fn`. -/
private theorem castKl'_dep_fn_sum {ιL ιR : Type} {F : ιL ⊕ ιR → ℕ × Type × Type}
    {a b : ιL ⊕ ιR} (hab : a = b)
    (f : ∀ k, (F k).2.1 → SPComp (F k).2.2)
    (eq : F a = F b) :
    castKl' eq (f a) = f b := by subst hab; rfl

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
      simp only [show ¬(I.ops.length + j.val < I.ops.length) by omega, dite_false]
      -- The elaborator cannot infer the `Fin` term for `Fin.ext` here;
      -- supply it explicitly. The Fin equality transports the chained
      -- `castKl'` to a single one via `castKl'_dep_fn`.
      have hval : (⟨I.ops.length + j.val - I.ops.length, by omega⟩ : Fin J.ops.length) = j :=
        Fin.ext (by show I.ops.length + j.val - I.ops.length = j.val; omega)
      -- Collapse the chained cast to a single one via proof irrelevance,
      -- then apply the dependent-function transport `castKl'_dep_fn` at the
      -- right summand index `Fin J.ops.length`.
      have key : ∀ (a : Fin J.ops.length)
          (eq_outer : (I.ops ++ J.ops).get ⟨I.ops.length + j.val, by simp⟩ = J.ops.get j)
          (eq_inner : J.ops.get a = (I.ops ++ J.ops).get ⟨I.ops.length + j.val, by simp⟩)
          (ha : a = j),
          castKl' eq_outer (castKl' eq_inner (h (.inr a))) = h (.inr j) := by
        intro a eq_outer eq_inner ha
        subst ha
        exact castKl'_castKl'_symm _ _ _
      exact key _ _ _ hval

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
  have he : diAppend (diAppend I J) K = diAppend I (diAppend J K) :=
    diAppend_assoc I J K
  rcases k with i | (j | l)
  all_goals simp only [pkg_comp_apply, tensorAppendIso_hom, appendAssocIso_hom]
  · -- I branch (Sum.inl i): LHS and RHS both reduce to two nested `castKl'`
    -- applied to `h ⟨i.val, _⟩`. Use a key lambda over both Fins with subst.
    show appendToTensor I J (fun i' => appendToTensor (diAppend I J) K h (Sum.inl i'))
          (Sum.inl i)
        = appendToTensor I (diAppend J K) (eqToHom (congrArg toPI he) h) (Sum.inl i)
    simp only [appendToTensor]
    rw [eqToHom_handler, handler_transport_apply he]
    · rcases i with ⟨i, hi⟩
      have key : ∀ (a b : Fin (diAppend (diAppend I J) K).ops.length) (hab : a = b)
          {t₁L t₂L t₁R t₂R : ℕ × Type × Type}
          (eqL1 : (diAppend (diAppend I J) K).ops.get a = t₁L) (eqL2 : t₁L = t₂L)
          (eqR1 : (diAppend (diAppend I J) K).ops.get b = t₁R) (eqR2 : t₁R = t₂R)
          (hT : t₂L = t₂R),
          castKl' eqL2 (castKl' eqL1 (h a)) =
            hT ▸ castKl' eqR2 (castKl' eqR1 (h b)) := by
        intro a b hab t₁L t₂L t₁R t₂R eqL1 eqL2 eqR1 eqR2 hT
        subst hab; subst eqL1; subst eqL2; subst eqR1; subst eqR2; rfl
      exact key _ _ (Fin.ext rfl) _ _ _ _ rfl
    · exact he
  · -- J branch (Sum.inr (Sum.inl j)): LHS has 2 nested castKl' applied to
    -- `h ⟨I.ops.length + j.val, _⟩`; RHS has 3 (extra cast from
    -- `handler_transport_apply he`). Use a key lambda that absorbs the chain
    -- by subst on the Fin index equality.
    show appendToTensor I J (fun i' => appendToTensor (diAppend I J) K h (Sum.inl i'))
          (Sum.inr j)
        = appendToTensor J K (fun j' =>
            appendToTensor I (diAppend J K) (eqToHom (congrArg toPI he) h) (Sum.inr j'))
          (Sum.inl j)
    simp only [appendToTensor]
    rw [eqToHom_handler, handler_transport_apply he]
    · rcases j with ⟨j, hj⟩
      have key : ∀ (a b : Fin (diAppend (diAppend I J) K).ops.length) (hab : a = b)
          {t₁L t₂L t₁R t₂R t₃R : ℕ × Type × Type}
          (eqL1 : (diAppend (diAppend I J) K).ops.get a = t₁L) (eqL2 : t₁L = t₂L)
          (eqR1 : (diAppend (diAppend I J) K).ops.get b = t₁R) (eqR2 : t₁R = t₂R)
          (eqR3 : t₂R = t₃R) (hT : t₂L = t₃R),
          castKl' eqL2 (castKl' eqL1 (h a)) =
            hT ▸ castKl' eqR3 (castKl' eqR2 (castKl' eqR1 (h b))) := by
        intro a b hab t₁L t₂L t₁R t₂R t₃R eqL1 eqL2 eqR1 eqR2 eqR3 hT
        subst hab; subst eqL1; subst eqL2; subst eqR1; subst eqR2; subst eqR3; rfl
      exact key _ _ (Fin.ext rfl) _ _ _ _ _ rfl
    · exact he
  · -- K branch (Sum.inr (Sum.inr l)): LHS has 1 castKl' applied to
    -- `h ⟨(I.ops.length + J.ops.length) + l.val, _⟩`; RHS has 3 casts applied
    -- to `h ⟨I.ops.length + (J.ops.length + l.val), _⟩`. Indices differ by
    -- Nat-addition-assoc.
    show appendToTensor (diAppend I J) K h (Sum.inr l)
        = appendToTensor J K (fun j' =>
            appendToTensor I (diAppend J K) (eqToHom (congrArg toPI he) h) (Sum.inr j'))
          (Sum.inr l)
    simp only [appendToTensor]
    rw [eqToHom_handler, handler_transport_apply he]
    · rcases l with ⟨l, hl⟩
      have key : ∀ (a b : Fin (diAppend (diAppend I J) K).ops.length) (hab : a = b)
          {t₁L t₁R t₂R t₃R : ℕ × Type × Type}
          (eqL1 : (diAppend (diAppend I J) K).ops.get a = t₁L)
          (eqR1 : (diAppend (diAppend I J) K).ops.get b = t₁R) (eqR2 : t₁R = t₂R)
          (eqR3 : t₂R = t₃R) (hT : t₁L = t₃R),
          castKl' eqL1 (h a) =
            hT ▸ castKl' eqR3 (castKl' eqR2 (castKl' eqR1 (h b))) := by
        intro a b hab t₁L t₁R t₂R t₃R eqL1 eqR1 eqR2 eqR3 hT
        subst hab; subst eqL1; subst eqR1; subst eqR2; subst eqR3; rfl
      exact key _ _ (Fin.ext (by simp [diAppend, DeepInterface.append]; omega))
        _ _ _ _ rfl
    · exact he

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
  show appendToTensor I ⟨[]⟩ h (Sum.inl k) = _
  simp only [appendToTensor]
  have he : diAppend I ⟨[]⟩ = I := diAppend_empty_right I
  rw [show (appendEmptyRightIso I).hom =
        eqToHom (congrArg toPI he) from rfl,
      eqToHom_handler, handler_transport_apply he]
  · rfl
  · exact he

/-- Left unitor coherence: the two paths from `toPI(⟨[]⟩ ++ I)` to `toPI(I)` agree.
    Path 1: `toPI(⟨[]⟩++I) → toPI(⟨[]⟩) ⊗ toPI(I) → 𝟙_ ⊗ toPI(I) → toPI(I)`
    Path 2: `toPI(⟨[]⟩++I) → toPI(I)` directly via `appendEmptyLeftIso`. -/
theorem tensorAppend_leftUnitor_coherence :
    (tensorAppendIso ⟨[]⟩ I).hom ≫ (unitIso.hom ▷ toPI I) ≫ (λ_ (toPI I)).hom =
    (appendEmptyLeftIso I).hom := by
  funext h k
  simp [unitIso, appendEmptyLeftIso]
  exact castKl'_dep_fn (Fin.ext (Nat.zero_add k.val)) h _

/-! ## Braiding Bridge -/

/-- Braiding bridge: composing the tensor-append iso with braiding and the
    inverse tensor-append iso gives the concrete swap. -/
noncomputable def diAppend_braiding_iso :
    toPI (diAppend I J) ≅ toPI (diAppend J I) :=
  tensorAppendIso I J ≪≫ (β_ (toPI I) (toPI J)) ≪≫ (tensorAppendIso J I).symm

end CatCrypt.Bridge.MonoidalBridge
