/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XPredCore

/-!
# `XFrameHet`: the frame rule along a separating map across assertion types

The frame rule of `XCorePT` (`XCorePT.frame`) relates one transformer to itself over one
assertion type. A frame that enlarges the state changes both: a separating map
`sep : P₁ → P₂ → P₃` takes an assertion on the small state and a frame assertion to an
assertion on the large state, and the program on the large state is a second transformer
`t' : XCorePT P₃ EPred G' α`. Locality of the pair `(t, t')` along `sep` is required only at
the postconditions satisfying an admissibility predicate `adm`; `adm = fun _ => True` asks
for it at all postconditions.

## Main definitions

* `XCorePT.LocalAlong sep adm t t'`: at every admissible postcondition, the framed weakest
  precondition of `t` entails the weakest precondition of `t'` at the framed postcondition.

## Main results

* `XCorePT.frameAlong`: for `sep` monotone in its first argument, a triple of `t` at an
  admissible postcondition gives the triple of `t'` with the framed pre- and postcondition.
* `XCorePT.local_iff_localAlong`: `XCorePT.Local` is locality along `XCoreSep.sep` of the
  pair `(t, t)` at all postconditions; `XCorePT.frame_of_frameAlong` derives the
  conclusion of `XCorePT.frame` from `frameAlong`.
* `XCorePT.ret_localAlong`, `XCorePT.bind_localAlong`, `XCorePT.seq_localAlong`: closure of
  locality along `sep` under return, bind and sequencing.
-/

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.XDijkstra

universe u₁ u₂ u₃ v w w' x y

namespace XCorePT

variable {P₁ : Type u₁} {P₂ : Type u₂} {P₃ : Type u₃} {EPred : Type v}
  {G : Type w} {G' : Type w'} {α : Type x} {β : Type y}

/-- Locality of a pair of transformers along a separating map `sep : P₁ → P₂ → P₃`, at the
postconditions satisfying `adm`: the weakest precondition of `t` framed by `R` entails the
weakest precondition of `t'` at the postcondition framed by `R`. -/
def LocalAlong [LE P₁] [LE P₃] [LE EPred] (sep : P₁ → P₂ → P₃)
    (adm : (α → P₁) → Prop) (t : XCorePT P₁ EPred G α) (t' : XCorePT P₃ EPred G' α) : Prop :=
  ∀ (post : α → P₁), adm post → ∀ (epost : EPred) (R : P₂),
    sep (t.apply post epost) R ≤ t'.apply (fun a => sep (post a) R) epost

/-- **The frame rule along a separating map.** For `sep` monotone in its first argument and a
pair `(t, t')` local along `sep` at the admissible postcondition `post`, a triple of `t` from
`P` to `post` gives the triple of `t'` from `sep P R` to `sep (post a) R`. -/
theorem frameAlong [LE P₁] [Preorder P₃] [LE EPred] {sep : P₁ → P₂ → P₃}
    (hsep : ∀ {a b : P₁} (r : P₂), a ≤ b → sep a r ≤ sep b r) {adm : (α → P₁) → Prop}
    {t : XCorePT P₁ EPred G α} {t' : XCorePT P₃ EPred G' α} (hloc : LocalAlong sep adm t t')
    {P : P₁} {post : α → P₁} {epost : EPred} (hadm : adm post) (R : P₂)
    (h : Triple P t post epost) :
    Triple (sep P R) t' (fun a => sep (post a) R) epost :=
  le_trans (hsep R h) (hloc post hadm epost R)

/-- `XCorePT.Local` is locality of `(t, t)` along `XCoreSep.sep` at all postconditions. -/
theorem local_iff_localAlong [LE P₁] [LE EPred] [XCoreSep P₁] {t : XCorePT P₁ EPred G α} :
    t.Local ↔ LocalAlong XCoreSep.sep (fun _ => True) t t :=
  ⟨fun h post _ epost R => h post epost R, fun h post epost R => h post trivial epost R⟩

/-- The frame rule `XCorePT.frame` as the diagonal case of `frameAlong`. -/
theorem frame_of_frameAlong [Preorder P₁] [LE EPred] [XCoreSep P₁]
    {t : XCorePT P₁ EPred G α} (hloc : t.Local) {P R : P₁} {post : α → P₁} {epost : EPred}
    (h : Triple P t post epost) :
    Triple (XCoreSep.sep P R) t (fun a => XCoreSep.sep (post a) R) epost :=
  frameAlong (fun r => XCoreSep.sep_mono_left r) (local_iff_localAlong.1 hloc) trivial R h

/-- Return is local along every separating map, at every postcondition. -/
theorem ret_localAlong [LE P₁] [Preorder P₃] [LE EPred] [Zero G] [Zero G']
    (sep : P₁ → P₂ → P₃) (adm : (α → P₁) → Prop) (a : α) :
    LocalAlong sep adm (ret (Pred := P₁) (EPred := EPred) (G := G) a)
      (ret (Pred := P₃) (EPred := EPred) (G := G') a) :=
  fun _ _ _ _ => le_rfl

/-- Locality along `sep` is closed under bind, when the head is local at the intermediate
postconditions `fun a => (f a).apply post epost` of every admissible `post`. -/
theorem bind_localAlong [LE P₁] [Preorder P₃] [Preorder EPred] {sep : P₁ → P₂ → P₃}
    {adm₁ : (α → P₁) → Prop} {adm : (β → P₁) → Prop}
    {s : XCorePT P₁ EPred G α} {s' : XCorePT P₃ EPred G' α}
    {f : α → XCorePT P₁ EPred G β} {f' : α → XCorePT P₃ EPred G' β}
    (hs : LocalAlong sep adm₁ s s') (hf : ∀ a, LocalAlong sep adm (f a) (f' a))
    (hadm : ∀ post epost, adm post → adm₁ (fun a => (f a).apply post epost)) :
    LocalAlong sep adm (s.bind f) (s'.bind f') := fun post hpost epost R =>
  le_trans (hs _ (hadm post epost hpost) epost R)
    (s'.mono (fun a => hf a post hpost epost R) le_rfl)

/-- Locality along `sep` is closed under sequencing, when the head is local at the constant
postconditions `fun _ => t.apply post epost` of every admissible `post`. -/
theorem seq_localAlong [LE P₁] [Preorder P₃] [Preorder EPred] [Add G] [Add G']
    {sep : P₁ → P₂ → P₃} {adm₁ : (α → P₁) → Prop} {adm : (β → P₁) → Prop}
    {s : XCorePT P₁ EPred G α} {s' : XCorePT P₃ EPred G' α}
    {t : XCorePT P₁ EPred G β} {t' : XCorePT P₃ EPred G' β}
    (hs : LocalAlong sep adm₁ s s') (ht : LocalAlong sep adm t t')
    (hadm : ∀ post epost, adm post → adm₁ (fun _ => t.apply post epost)) :
    (s.seq t).LocalAlong sep adm (s'.seq t') := fun post hpost epost R =>
  le_trans (hs _ (hadm post epost hpost) epost R)
    (s'.mono (fun _ => ht post hpost epost R) le_rfl)

end XCorePT

end CatCrypt.XDijkstra
